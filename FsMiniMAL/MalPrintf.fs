module FsMiniMAL.MalPrintf

open System
open System.Text
open System.Collections.Generic
open Microsoft.FSharp.Core

open Types
open Syntax
open Value
open System.Reflection
open PrintfFormat

let arity_of_cmds cmds = 
    let rec loop accu cmds = 
        match cmds with
        | PrintfCommand.Spec _ :: t -> loop (accu + 1) t
        | PrintfCommand.Text _ :: t -> loop accu t
        | [] -> accu
    loop 0 cmds

let sprintf_d = 
    [| sprintf "%*d"
       sprintf "%-*d"
       sprintf "%0*d"
       sprintf "%0-*d"
       sprintf "%+*d"
       sprintf "%+-*d"
       sprintf "%+0*d"
       sprintf "%+0-*d"
       sprintf "% *d"
       sprintf "% -*d"
       sprintf "% 0*d"
       sprintf "% 0-*d" |]

let sprintf_x = 
    [| sprintf "%*x"
       sprintf "%-*x"
       sprintf "%0*x"
       sprintf "%0-*x"
       sprintf "%+*x"
       sprintf "%+-*x"
       sprintf "%+0*x"
       sprintf "%+0-*x"
       sprintf "% *x"
       sprintf "% -*x"
       sprintf "% 0*x"
       sprintf "% 0-*x" |]

let sprintf_X = 
    [| sprintf "%*X"
       sprintf "%-*X"
       sprintf "%0*X"
       sprintf "%0-*X"
       sprintf "%+*X"
       sprintf "%+-*X"
       sprintf "%+0*X"
       sprintf "%+0-*X"
       sprintf "% *X"
       sprintf "% -*X"
       sprintf "% 0*X"
       sprintf "% 0-*X" |]

let sprintf_f = 
    [| sprintf "%*.*f"
       sprintf "%-*.*f"
       sprintf "%0*.*f"
       sprintf "%0-*.*f"
       sprintf "%+*.*f"
       sprintf "%+-*.*f"
       sprintf "%+0*.*f"
       sprintf "%+0-*.*f"
       sprintf "% *.*f"
       sprintf "% -*.*f"
       sprintf "% 0*.*f"
       sprintf "% 0-*.*f" |]

let sprintf_e = 
    [| sprintf "%*.*e"
       sprintf "%-*.*e"
       sprintf "%0*.*e"
       sprintf "%0-*.*e"
       sprintf "%+*.*e"
       sprintf "%+-*.*e"
       sprintf "%+0*.*e"
       sprintf "%+0-*.*e"
       sprintf "% *.*e"
       sprintf "% -*.*e"
       sprintf "% 0*.*e"
       sprintf "% 0-*.*e" |]

let sprintf_E = 
    [| sprintf "%*.*E"
       sprintf "%-*.*E"
       sprintf "%0*.*E"
       sprintf "%0-*.*E"
       sprintf "%+*.*E"
       sprintf "%+-*.*E"
       sprintf "%+0*.*E"
       sprintf "%+0-*.*E"
       sprintf "% *.*E"
       sprintf "% -*.*E"
       sprintf "% 0*.*E"
       sprintf "% 0-*.*E" |]

let sprintf_g = 
    [| sprintf "%*.*g"
       sprintf "%-*.*g"
       sprintf "%0*.*g"
       sprintf "%0-*.*g"
       sprintf "%+*.*g"
       sprintf "%+-*.*g"
       sprintf "%+0*.*g"
       sprintf "%+0-*.*g"
       sprintf "% *.*g"
       sprintf "% -*.*g"
       sprintf "% 0*.*g"
       sprintf "% 0-*.*g" |]

let sprintf_G = 
    [| sprintf "%*.*G"
       sprintf "%-*.*G"
       sprintf "%0*.*G"
       sprintf "%0-*.*G"
       sprintf "%+*.*G"
       sprintf "%+-*.*G"
       sprintf "%+0*.*G"
       sprintf "%+0-*.*G"
       sprintf "% *.*G"
       sprintf "% -*.*G"
       sprintf "% 0*.*G"
       sprintf "% 0-*.*G" |]


let exec_cmds cmds (argv : value array) =
    let sb = new StringBuilder()
    let mutable i = 0
    for cmd in cmds do
        match cmd with
        | Text s -> sb.Add(s)
        | Spec({ TypeChar = 's' } as spec) -> 
            let s = to_string argv.[i]
            
            let s = 
                if 0 <= spec.Width then 
                    if spec.Flags.HasFlag(Flags.LeftJustify) then s.PadRight(spec.Width)
                    else s.PadLeft(spec.Width)
                else s
            sb.Add(s)
            i <- i + 1
        | Spec({ TypeChar = ('d' | 'x' | 'X') } as fmt) -> 
            let w = 
                if 0 <= fmt.Width then fmt.Width
                else 0
            
            let f = 
                (match fmt.TypeChar with
                 | 'd' -> sprintf_d
                 | 'x' -> sprintf_x
                 | 'X' -> sprintf_X
                 | _ -> raise InvalidFormatString).[int fmt.Flags]
            
            let n = Value.to_int argv.[i]
            let s = f w n
            sb.Add(s)
            i <- i + 1
        | Spec({ TypeChar = ('f' | 'e' | 'E' | 'g' | 'G') } as fmt) -> 
            let w = 
                if 0 <= fmt.Width then fmt.Width
                else 0
            
            let p = 
                if 0 <= fmt.Precision then fmt.Precision
                else 6
            
            let f = 
                (match fmt.TypeChar with
                 | 'f' -> sprintf_f
                 | 'e' -> sprintf_e
                 | 'E' -> sprintf_E
                 | 'g' -> sprintf_g
                 | 'G' -> sprintf_G
                 | _ -> raise InvalidFormatString).[int fmt.Flags]
            
            let x = Value.to_float argv.[i]
            let s = f w p x
            sb.Add(s)
            i <- i + 1
        | Spec({ TypeChar = 'r' } as fmt) ->
            let x = Value.to_float argv.[i]
            let s = Misc.string_of_float x
            sb.Add(s)
            i <- i + 1            
        | Spec _ -> raise InvalidFormatString
    sb.ToString()

