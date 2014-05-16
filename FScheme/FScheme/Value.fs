module FScheme.Value

open FScheme.Thunk

open ExtCore.Collections
open System

///Types of FScheme values
type Value =
   ///Value representing any .NET object.
   | Container of obj
   ///Value representing a number (double).
   | Number of double
   ///Value representing a string.
   | String of string
   ///Value representing a symbol.
   | Symbol of string
   ///Booleans
   | Bool of bool
   ///Data structures
   | Data of DataCon
   ///Value representing a function.
   | Function of Func
   ///Value representing an invalid value (used for mutation, where Values shouldn't return anything).
   ///Should NOT be used except internally by this interpreter.
   | Dummy of string

and DataCon = { name: string; fields: Thunk array }

///Type of all functions
and Func = Thunk list -> Continuation -> Value

///Delayed computations
and Thunk = Thunk.Thunk<Value, Value>

///Function that takes a Value and returns a Value.
and Continuation = Value -> Value

///Forces evaluation of a Thunk
let force (cps: Thunk) = runCPS cps id

///FScheme Function delegate. Takes a list of Values as arguments, and returns a Value.
type ExternFunc = delegate of Thunk list -> Value

///Makes a Value.Function out of an ExternFunc
let makeExternFunc (externFunc : ExternFunc) = Function(externFunc.Invoke >> (|>))

//Converts the given Value to a string.
let rec print = function
   | String(s) -> "\"" + s + "\""
   | Symbol(s) -> s
   | Number(n) -> n.ToString()
   | Container(o) -> o.ToString()
   | Function(_) -> "#<procedure>"
   | Dummy(_) -> "" // sometimes useful to emit value for debugging, but normally we ignore
   | Bool(b) -> if b then "#t" else "#f"
   | Data(d) -> printDataCon d

and printDataCon d =
    if d.name = "nil" then
        "()"
    else if d.fields.Length = 0 then
        d.name
    else if d.name = "cons" then
        let toList' (data: DataCon) : Value list = 
            let rec toList (a: Value list) : DataCon -> Value list = function
                | { name="cons"; fields=[| h; t |] } ->
                    match force t with
                    | Data(d) -> toList (force h::a) d
                    | m -> print m |> sprintf "Cannot convert %s to list" |> failwith
                | { name="nil" } -> List.rev a
                | m -> printDataCon m |> sprintf "Cannot convert %s to list" |> failwith
            toList [] data
        let parameters = String.Join(" ", List.map print <| toList' d)
        sprintf "(%s)" parameters
    else
        let parameters = String.Join(" ", Seq.map (force >> print) d.fields)
        sprintf "(%s %s)" d.name parameters

module List =

    let isNil { name=name } = name = "nil"
    let nil = Data({ name="nil"; fields=[||] })
    let cons h t = Data({ name="cons"; fields=[| h; t |]})
    let car = function
        | { name="cons"; fields=[| h; _ |] } -> h
        | m -> printDataCon m |> sprintf "bad car arg: %s" |> failwith
    let cdr = function
        | { name="cons"; fields=[| _; t |] } -> t
        | m -> printDataCon m |> sprintf "bad cdr arg: %s" |> failwith

    let thunkList : Thunk list -> Value = List.rev >> List.fold (fun a t -> cons t (constant a)) nil
    let valList : Value list -> Value = List.map constant >> thunkList

    let toList (data: DataCon) = 
        let rec toList (a: Thunk list) : DataCon -> CPS<_, _> = function
            | { name="cons"; fields=[| h; t |] } ->
                cps {
                    let! v = t
                    match v with
                    | Data(d) -> return! toList (h::a) d
                    | m -> return print m |> sprintf "Cannot convert %s to list" |> failwith }
            | { name="nil" } -> cps { return List.rev a }
            | m -> printDataCon m |> sprintf "Cannot convert %s to list" |> failwith
        toList [] data

    let concat a (b: Value) =
        let rec append (a: Value) = function
            | [] -> cps { return a }
            | h::t -> cps { return! append (cons h <| constant a) t }
        cps {
            let! startList = toList a
            return! append b <| List.rev startList }

    let take n data =
        let rec take n a data =
            if n <= 0 then 
                cps { return List.rev a |> thunkList } 
            else
                match data with
                | { name="cons"; fields=[| h; t |] } ->
                    cps {
                        let! list = t
                        match list with
                        | Data(list) -> return! take (n - 1) (h :: a) list 
                        | m -> return print m |> sprintf "Cannot convert %s to list" |> failwith }
                | { name="nil" } -> cps { return List.rev a |> thunkList }
                | m -> printDataCon m |> sprintf "Cannot convert %s to list" |> failwith
        take n [] data

    let rec drop n data =
        if n <= 0 then 
            cps { return Data(data) }
        else
            match data with
            | { name="cons"; fields=[| _; t |] } ->
                cps {
                    let! list = t
                    match list with
                    | Data(list) -> return! drop (n - 1) list 
                    | m -> return print m |> sprintf "Cannot convert %s to list" |> failwith }
            | { name="nil" } -> cps { return nil }
            | m -> printDataCon m |> sprintf "Cannot convert %s to list" |> failwith

    let rec get n data =
        match data with
        | { name="cons"; fields=[| h; _ |] } when n <= 0 -> h
        | { name="cons"; fields=[| _; t |] } when n <> 0 ->
            cps {
                let! list = t
                match list with
                | Data(list) -> return! get (n - 1) list 
                | m -> return print m |> sprintf "Cannot convert %s to list" |> failwith }
        | { name="nil" } -> failwith "Index out of bounds."
        | m -> printDataCon m |> sprintf "Cannot convert %s to list" |> failwith