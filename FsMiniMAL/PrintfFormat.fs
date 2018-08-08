// Derived from https://github.com/Microsoft/visualfsharp/blob/master/src/fsharp/FSharp.Core/printf.fs
// This file is licensed in MIT License.
// Copyright (c) Microsoft Corporation.  All Rights Reserved.
// Copyright (c) Nozomi Shibano
module FsMiniMAL.PrintfFormat

open System

[<Flags>]
type Flags = 
    | None = 0
    | LeftJustify = 1
    | PadWithZeros = 2
    | PlusForPositives = 4
    | SpaceForPositives = 8

[<Literal>]
let StarValue = -1

[<Literal>]
let NotSpecifiedValue = -2

type Spec = 
    { TypeChar : char
      Precision : int
      Width : int
      Flags : Flags }

type PrintfCommand = 
    | Text of string
    | Spec of Spec

exception InvalidFormatString

let isDigit c = c >= '0' && c <= '9'

let intFromString (s : string) pos = 
    let rec go acc i = 
        if isDigit s.[i] then 
            let n = int s.[i] - int '0'
            go (acc * 10 + n) (i + 1)
        else acc, i
    go 0 pos

let parseFlags (s : string) i : Flags * int = 
    let rec go flags i = 
        match s.[i] with
        | '0' -> go (flags ||| Flags.PadWithZeros) (i + 1)
        | '+' -> go (flags ||| Flags.PlusForPositives) (i + 1)
        | ' ' -> go (flags ||| Flags.SpaceForPositives) (i + 1)
        | '-' -> go (flags ||| Flags.LeftJustify) (i + 1)
        | _ -> flags, i
    go Flags.None i

let parseWidth (s : string) i : int * int = 
    if s.[i] = '*' then StarValue, (i + 1)
    elif isDigit (s.[i]) then intFromString s i
    else NotSpecifiedValue, i

let parsePrecision (s : string) i : int * int = 
    if s.[i] = '.' then 
        if s.[i + 1] = '*' then StarValue, i + 2
        elif isDigit (s.[i + 1]) then intFromString s (i + 1)
        else raise InvalidFormatString // invalid precision value
    else NotSpecifiedValue, i

let parseTypeChar (s : string) i : char * int = s.[i], (i + 1)

let findNextFormatSpecifier (s : string) i = 
    let rec go i (buf : Text.StringBuilder) = 
        if i >= s.Length then s.Length, buf.ToString()
        else 
            let c = s.[i]
            if c = '%' then 
                if i + 1 < s.Length then 
                    let _, i1 = parseFlags s (i + 1)
                    let w, i2 = parseWidth s i1
                    let p, i3 = parsePrecision s i2
                    let typeChar, i4 = parseTypeChar s i3
                    // shortcut for the simpliest case
                    // if typeChar is not % or it has star as width\precision - resort to long path
                    if typeChar = '%' && not (w = StarValue || p = StarValue) then 
                        buf.Append('%') |> ignore
                        go i4 buf
                    else i, buf.ToString()
                else raise InvalidFormatString // (ArgumentException("Missing format specifier"))
            else 
                buf.Append(c) |> ignore
                go (i + 1) buf
    go i (Text.StringBuilder())

let rec parse_fmt_from_formatspec (s : string) (i : int) = 
    if i = s.Length then []
    else 
        if s.[i] <> '%' then raise InvalidFormatString
        let flags, i = parseFlags s (i + 1)
        let width, i = parseWidth s i
        let precision, i = parsePrecision s i
        let typeChar, i = parseTypeChar s i
        let i, suffix = findNextFormatSpecifier s i
        match typeChar with
        | 's' | 'd' | 'x' | 'X' | 'f' | 'e' | 'E' | 'g' | 'G' | 'r' -> ()
        | _ -> raise InvalidFormatString
        let spec = 
            { TypeChar = typeChar
              Precision = precision
              Flags = flags
              Width = width }
        (PrintfCommand.Spec spec) :: (Text suffix) :: parse_fmt_from_formatspec s i

let parse_fmt (fmt : string) = 
    let pos, prefix = findNextFormatSpecifier fmt 0
    if prefix.Length = 0 then parse_fmt_from_formatspec fmt pos
    else Text prefix :: parse_fmt_from_formatspec fmt pos
