namespace FsMiniMAL

open System.Collections.Immutable

type alloc = 
    { mutable EnvSize : int // size of env
      mutable Locals : ImmutableDictionary<string, int * access> // variables in local scope
      OuterLocals : ImmutableDictionary<string, int * access> list // variables in outer local scope
      mutable Captured : ImmutableDictionary<string, int * access> // variables captured from outer local scope
                                                        }
    static member Create() = 
        { EnvSize = 0
          Locals = ImmutableDictionary.Empty
          OuterLocals =  []
          Captured = ImmutableDictionary.Empty }
    
    member this.Allocate() = 
        let ofs = this.EnvSize
        this.EnvSize <- this.EnvSize + 1
        ofs
    
    member this.Get(name : string) = 
        match this.Locals.TryGetValue(name) with
        | true, info -> info
        | false, _ -> 
            match this.Captured.TryGetValue(name) with
            | true, info -> info
            | false, _ ->
                let rec loop (l : ImmutableDictionary<string, int * access> list) =
                    match l with
                    | h :: t ->
                        match h.TryGetValue(name) with
                        | true, (_, access) -> 
                            let ofs = this.Allocate()
                            let info = (ofs, access)
                            this.Captured <- this.Captured.SetItem(name, info)
                            info
                        | false, _ -> loop t
                    | [] -> dontcare()
                loop this.OuterLocals
    
    member this.Add(name : string, access) = 
        let ofs = this.Allocate()
        this.Locals <- this.Locals.SetItem(name, (ofs, access))
        ofs

    member this.CreateNewEnv() = 
        { EnvSize = 0
          Locals = ImmutableDictionary.Empty
          Captured = ImmutableDictionary.Empty
          OuterLocals = this.Locals :: this.OuterLocals }
    
    member this.Clone() =
        { EnvSize = this.EnvSize
          Locals = this.Locals
          Captured = this.Captured
          OuterLocals = this.OuterLocals }
