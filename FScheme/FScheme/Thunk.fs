module FScheme.Thunk

let flip f x y = f y x

type CPS<'r, 'a> = ('a -> 'r) -> 'r
type Thunk<'a, 'b> = CPS<'b, 'a>

let constant (x: 'a) (c: 'a -> 'b) : 'b = c x

let runCPS = (<|)

let make_thunk (f: CPS<'b, 'a>) : Thunk<'a, 'b> =
    let box : 'a option ref = ref None
    fun c ->
        match !box with
        | Some(v) -> c v
        | None ->
            f (fun v -> box := Some(v); c v)

module Cont =
    let bind (m: CPS<'r, 'a>) (f: 'a -> CPS<'r, 'b>) = (fun c -> m (fun a -> f a c))

type ContBuilder() =
    member x.Bind(m, f) = Cont.bind m f
    member x.Return(y) = constant y
    member x.ReturnFrom(v) = v
    member x.Zero() = fun _ -> ()
let cps = ContBuilder()

let rec sequence ms = 
    let k m m' = 
        cps {
            let! x = m
            let! xs = m'
            return x::xs }
    List.foldBack k ms (constant [])