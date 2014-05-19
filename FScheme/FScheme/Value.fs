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

let ValueToBool = function
    | Bool(b) -> b
    | Number(0.) -> false
    | Data({name="nil"}) -> false
    | String("") -> false
    | _ -> true

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
   | Container(o) -> sprintf "#<object:\"%s\">" <| o.ToString()
   | Function(_) -> "#<procedure>"
   | Dummy(_) -> "#<undefined>" // sometimes useful to emit value for debugging, but normally we ignore
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
    let nil = { name="nil"; fields=[||] }
    let cons h t = { name="cons"; fields=[| h; t |]}
    let car = function
        | { name="cons"; fields=[| h; _ |] } -> h
        | m -> printDataCon m |> sprintf "bad car arg: %s" |> failwith
    let car' = function
        | Data(d) -> car d
        | m -> print m |> sprintf "bad car arg: %s" |> failwith
    let cdr = function
        | { name="cons"; fields=[| _; t |] } -> t
        | m -> printDataCon m |> sprintf "bad cdr arg: %s" |> failwith
    let cdr' = function
        | { name="cons"; fields=[| _; t |] } ->
            t ||> function Data(d) -> d 
                         | m -> print m |> sprintf "bad cons arg: %s is not a list" |> failwith
        | m -> printDataCon m |> sprintf "bad cdr arg: %s" |> failwith

    let thunkList' : Thunk list -> DataCon = List.rev >> List.fold (fun a t -> cons t (constant <| Data(a))) nil
    let thunkList = thunkList' >> Data
    let valList' : Value list -> DataCon = List.map constant >> thunkList'
    let valList = valList' >> Data

    let toList (data: DataCon) = 
        let rec toList (a: Thunk list) (d: DataCon) : CPS<_, _> =
            if isNil d |> not then
                cdr' d >>= toList (car d::a)
            else
                cps { return List.rev a }
        toList [] data

    let concat a (b: Thunk) =
        let rec concat b a =
            if isNil a then
                b ||> function Data(d) -> d
                             | m -> print m |> sprintf "bad concat arg: %s is not a list" |> failwith
            else
                let h = car a
                cps { return cdr' a >>= concat b ||> Data |> cons h }
        concat b a
    
    let rec take n data =
        if n <= 0 or isNil data then
            nil 
        else
            cdr' data ||> take (n - 1) ||> Data |> cons (car data)

    let rec drop n data =
        if n <= 0 then 
            cps { return data }
        else if isNil data then
            cps { return nil }
        else
            cdr' data >>= drop (n - 1)

    let rec get n data =
        if isNil data then
            failwith "Index out of bounds."
        else if n <= 0 then
            car data
        else
            cdr' data >>= get (n - 1)