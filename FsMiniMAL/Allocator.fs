namespace FsMiniMAL

open System.Collections.Immutable

type alloc_info = { ofs : int; access : access; is_capture : bool }

type alloc = 
    { mutable EnvSize : int
      mutable MaxEnvSize : int
      mutable CaptureSize : int
      mutable EnvBindings : ImmutableDictionary<string, alloc_info>
      mutable Captures : ImmutableDictionary<string, alloc_info * alloc_info>
      Parent : alloc option }
    
    static member Create() = 
        { EnvSize = 0
          MaxEnvSize = 0
          CaptureSize = 0
          EnvBindings = ImmutableDictionary.Empty
          Captures = ImmutableDictionary.Empty
          Parent = None }
    
    member this.Allocate() = 
        let ofs = this.EnvSize
        this.EnvSize <- this.EnvSize + 1
        this.MaxEnvSize <- max this.MaxEnvSize this.EnvSize
        ofs
    
    member this.AllocateCapture() =
        let ofs = this.CaptureSize
        this.CaptureSize <- this.CaptureSize + 1
        ofs

    member this.Get(name : string) : alloc_info = 
        match this.EnvBindings.TryGetValue(name) with
        | true, info -> info
        | false, _ ->
            match this.Captures.TryGetValue(name) with
            | true, (_, info) -> info
            | _ ->
                let ofs_to = this.AllocateCapture()
                let info_from = this.Parent.Value.Get(name)
                let info_to = { ofs = ofs_to; access = info_from.access; is_capture = true }
                this.Captures <- this.Captures.SetItem(name, (info_from, info_to))
                info_to
    
    member this.Add(name : string, access : access) : int = 
        let ofs = this.Allocate()
        this.EnvBindings <- this.EnvBindings.SetItem(name, { ofs = ofs; access = access; is_capture = false })
        ofs
    
    member this.Begin() = (this.EnvSize, this.EnvBindings)

    member this.End(env_at_begin) =
        let size, bindings = env_at_begin
        this.EnvSize <- size
        this.EnvBindings <- bindings

    member this.CreateNewEnv() = 
        { EnvSize = 0
          MaxEnvSize = 0
          CaptureSize = 0
          EnvBindings = ImmutableDictionary.Empty
          Captures = ImmutableDictionary.Empty
          Parent = Some this }
    
    member this.Clone() =
        if this.Parent.IsSome then dontcare()

        { EnvSize = this.EnvSize
          MaxEnvSize = this.MaxEnvSize
          CaptureSize = this.CaptureSize
          EnvBindings = this.EnvBindings
          Captures = this.Captures
          Parent = this.Parent }
