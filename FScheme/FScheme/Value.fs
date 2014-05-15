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
   ///Value representing a list of sub Values.
   | List of LazyList<Thunk>
   ///Value representing a function.
   | Function of Func
   ///Value representing an invalid value (used for mutation, where Values shouldn't return anything).
   ///Should NOT be used except internally by this interpreter.
   | Dummy of string

///Type of all functions
and Func = Thunk list -> Continuation -> Value

///Delayed computations
and Thunk = Thunk.Thunk<Value, Value>

///Function that takes a Value and returns a Value.
and Continuation = Value -> Value

///Forces evaluation of a Thunk
let force cps = runCPS cps id

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
   | List(list) -> 
        String.Join(" ", (Seq.map (force >> print) list))
            |> sprintf "(%s)"