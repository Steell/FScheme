module FScheme.Library

open FScheme.Parser
open FScheme.Thunk
open FScheme.Value
open FScheme.Value.List

open ExtCore.Collections

///Prints a malformed statement error.
let malformed n e = sprintf "Malformed '%s': %s" n (print e) |> failwith

let private foldOp name op =
    let rec fold a args =
        cps {
            match args with
            | [] -> return a
            | arg::t -> 
                let! h = arg
                match h with
                | Number(b) -> return! fold (op a b) t
                | m -> return malformed (sprintf "%s arg" name) m }
    fold

///Simple wrapper for arithmatic operations.
let private mathbin (op: double -> double -> double) name = function
   //If the arguments coming in consist of at least two numbers...
   | arg1 :: arg2 :: args ->
     cps {
        let! n = arg1
        match n with
        | Number(n) ->
            let! n2 = arg2
            match n2 with
            | Number(n2) -> return! foldOp name op (op n n2) args ||> Number
            | m -> return malformed (sprintf "%s arg" name) m
        | m -> return malformed (sprintf "%s arg" name) m }
   //Otherwise, fail.
   | m -> malformed name <| thunkList m

let private math0 op name start exprs = 
    foldOp name op start exprs ||> Number
  

let private math1 op (op2: Func) unary name = function
  | [arg] -> arg ||> function Number(n) -> Number(unary n)
                            | m -> malformed name m
  | arg :: args ->
    cps {
        let! n = arg
        match n with
        | Number(n) ->
            let! x = op2 args
            return
                match x with
                | Number(x) -> Number(op n x)
                | m -> malformed (sprintf "%s arg" name) m
        | m -> return malformed (sprintf "%s arg" name) m }
  | m -> malformed name <| thunkList m

//Arithmatic functions
let Add : Func = math0 (+) "addition" 0.
let Subtract : Func = math1 (-) Add (fun x -> -x) "subtraction"
let Multiply : Func = math0 (*) "multiplication" 1.
let Divide : Func = math1 (/) Multiply ((/) 1.) "division"
let Modulus : Func = mathbin (%) "modulus"
let Exponent : Func = mathbin ( ** ) "exponent"

let Sqrt = function
    | [arg] -> arg ||> function Number(n) -> Number(System.Math.Sqrt n)
                              | m -> malformed "sqrt" m
    | m -> malformed "sqrt" <| thunkList m

///Simple wrapper for comparison operations.
let private boolMath (op : (System.IComparable -> System.IComparable -> bool)) name args =
   let comp a' b' = Bool(op a' b')
   match args with
   | [a; b] ->
       cps {
           let! a = a
           let! b = b
           return
               match a, b with
               | Number(a), Number(b) -> comp a b
               | String(a), String(b) -> comp a b
               | m -> malformed name (thunkList <| List.map constant [a; b]) }
   | m -> malformed name <| thunkList m

//Comparison operations.
let LTE : Func = boolMath (<=) "less-than-or-equals"
let GTE : Func = boolMath (>=) "greater-than-or-equals"
let LT : Func = boolMath (<) "less-than"
let GT : Func = boolMath (>) "greater-than"

let rec EQ = function
    | [arg1; arg2] as args ->
        cps {
            let! v1 = arg1
            let! v2 = arg2
            match v1, v2 with
            | Number(x1), Number(x2) -> return Bool(x1 = x2)
            | String(x1), String(x2) -> return Bool(x1 = x2)
            | Container(o1), Container(o2) -> return Bool(o1 = o2 || o1.Equals(o2))
            | Data(x1), Data(x2) ->
                let! l1 = toList x1
                let! l2 = toList x2
                let eq' x y =
                    cps {
                        let! value = EQ [x; y]
                        match value with Bool(b) -> return b | _ -> return false }
                let forall2 (p: Thunk -> Thunk -> CPS<_, _>) =
                    let rec forall (l1: Thunk list) (l2: Thunk list) =
                        cps {
                            match (l1, l2) with
                            | ([], _) | (_, []) -> return true
                            | (h1::t1, h2::t2) ->
                                let! result = p h1 h2
                                if not result then 
                                    return false 
                                else 
                                    return! forall t1 t2 }
                    forall
                let! b = forall2 eq' l1 l2
                return Bool(b) 
            | _ -> return malformed "=" <| thunkList args }
    | m -> malformed "=" <| thunkList m

let Not = function
    | [arg] -> 
        cps {
            let! value = arg
            return if ValueToBool value then Number(0.) else Number(1.) }
    | m -> malformed "not" <| thunkList m

let Xor = function
    | [arg1; arg2] as args ->
        cps {
            let! a = arg1
            let! b = arg2
            let b' = ValueToBool b
            let result = if ValueToBool a then not b' else b'
            return Bool(result) }
    | m -> malformed "xor" <| thunkList m

///Display construct -- used to print to stdout
let Display = function
   | [e] -> e ||> print ||> printf "DISPLAY: %s \n" ||> fun () -> Dummy("Dummy 'display'")
   | m -> malformed "display" <| thunkList m

let Add1 = function
   | [arg] -> arg ||> function Number(n) -> Number(n + 1.) | m -> malformed "add1" m
   | m -> malformed "add1" <| thunkList m

let Sub1 = function
   | [arg] -> arg ||> function Number(n) -> Number(n - 1.) | m -> malformed "sub1" m
   | m -> malformed "sub1" <| thunkList m

//Random Number
let private _r = new System.Random()
let RandomDbl = function
    | [] -> cps { return Number(_r.NextDouble()) }
    | m -> malformed "random" <| thunkList m

//List Functions
let IsEmpty = function
    | [arg] -> arg ||> function Data(d) -> Bool(isNil d) | _ -> Bool(false)
    | m -> malformed "empty?" <| thunkList m

let Cons = function 
    | [head; tail] -> cps { return Data(cons head tail) }
    | m -> malformed "cons" <| thunkList m

let Car : Func = function 
    | [arg] -> arg >>= function Data(d) -> car d | _ -> malformed "car" <| thunkList [arg]
    | m -> malformed "car" <| thunkList m

let Cdr : Func = function
    | [l] -> l >>= function Data(d) -> cdr d | _ -> malformed "cdr" <| thunkList [l]
    | m -> malformed "cdr" <| thunkList m

let Rev = function
    | [l] -> l >>= function Data(d) -> toList d ||> (List.rev >> thunkList) 
                          | m -> malformed "reverse" m
    | m -> malformed "reverse" <| thunkList m

let MakeList (args: Thunk list) = thunkList args |> constant

let Len = function
    | [l] -> l >>= function Data(d) -> toList d ||> List.length ||> double ||> Number
                          | m -> malformed "len" m
    | m -> malformed "len" <| thunkList m

let Append : Func = function
    | [l1; l2] ->
        cps {
            let! list1 = l1
            match list1 with
            | Data(l1) -> return! concat l1 l2 ||> Data
            | _ -> return malformed "append" <| thunkList [l1; l2] }
    | m -> malformed "append" <| thunkList m

let Take = function
    | [n; l] ->
        cps {
            let! amt = n
            let! list = l
            return 
                match amt, list with
                | Number(n), Data(l) -> Data(take (int n) l)
                | _ -> malformed "take" <| thunkList [n; l] }
    | m -> malformed "take" <| thunkList m

let Get = function
    | [n; l] ->
        cps {
            let! amt = n
            let! list = l
            match amt, list with
            | Number(n), Data(l) -> return! get (int n) l
            | _ -> return malformed "get" <| thunkList [n; l] }
    | m -> malformed "get" <| thunkList m

let Drop : Func = function
    | [n; l] ->
        cps {
            let! amt = n
            let! list = l
            match amt, list with
            | Number(n), Data(l) -> return! drop (int n) l ||> Data
            | _ -> return malformed "drop" <| thunkList [n; l] }
    | m -> malformed "drop" <| thunkList m

let Last = function
    | [listArg] as args ->
        cps {
            let! l = listArg
            match l with
            | Data(d) -> return! toList d ||> List.last
            | _ -> return malformed "last" <| thunkList args }
    | m -> malformed "last" <| thunkList m

///Sorts using natural ordering. Only works for primitive types (numbers, strings, etc.)
let Sort = function
   //We expect a list of Values as the only argument.
   | [l] ->
      cps {
          let! list = l
          match list with
          | Data(l) ->
              let! l = toList l
              if List.isEmpty l then
                  return malformed "sort" <| Data(nil)
              else
                  let! vals = sequence l
                  //Peek and see what kind of data we're sorting
                  let first = List.head vals
                  match first with
                  //If the first element is a Value.Number...
                  | Number(n) ->
                        //converter: Makes sure given Value is a Value.Number.
                        //           If it is a Value.Number, pull the Number from it.
                        //           Otherwise, fail.
                        let converter = function
                            | Number(n) -> n
                            | m -> malformed "sort" m
                        //Convert Value.Numbers to doubles, sort them, then convert them back to Value.Numbers.
                        return 
                            List.map converter vals
                                |> List.sort 
                                |> List.map (fun n -> cps { return Number(n) }) 
                                |> thunkList
                  //If the first element is a Value.String...
                  | String(s) ->
                        //converter: Makes sure given Value is a Value.String.
                        //           If it is a Value.String, pull the string from it.
                        //           Otherwise, fail.
                        let converter = function
                            | String(s) -> s
                            | m -> malformed "sort" m
                        //Convert Value.Strings to strings, sort them, then convert them back to Value.Strings.
                        return 
                            List.map converter vals 
                                |> List.sort 
                                |> List.map (fun n -> cps { return String(n) }) 
                                |> thunkList
                  | m -> return malformed "sort type" m
          | m ->  return malformed "sort" m }
   //Otherwise, fail.
   | m -> malformed "sort" <| thunkList m

///Build Sequence
let BuildSeq = function
   | [a1; a2; a3] as args ->
        cps {
            let! start = a1
            let! stop = a2
            let! step = a3
            return
                match start, stop, step with
                | Number(start), Number(stop), Number(step) -> 
                    [start .. step .. stop] 
                        |> List.map (Number >> constant) 
                        |> thunkList
                | _ -> malformed "build-seq" <| thunkList args }
   | m -> malformed "build-seq" <| thunkList m

let String2Num = function
    | [s] ->
        cps {
            let! string = s
            return
                match string with
                | String(s) -> Number(System.Convert.ToDouble(s))
                | m -> malformed "string" m }
    | m -> malformed "string" <| thunkList m

let Num2String = function
    | [n] ->
        cps {
            let! num = n
            return
                match num with
                | Number(n) -> String(n.ToString())
                | m -> malformed "number" m }
    | m -> malformed "number" <| thunkList m

let Concat = function
    | [l] ->
        cps {
            let! list = l
            match force l with
            | Data(d) -> 
                let rec concat a l =
                    cps {
                        if Seq.isEmpty l then
                            return String(a)
                        else
                            let! string = Seq.nth 0 l
                            match string with
                            | String(s) -> return! concat (a + s) (Seq.skip 1 l)
                            | m -> return malformed "string" m }
                let! l = toList d
                return! concat "" l
            | m -> return malformed "concat" m }
    | m -> malformed "concat" <| thunkList m

///Error construct
let Throw = function
   | [s] ->
        match force s with
        | String(s) -> failwith s
        | m -> malformed "throw" m
   | m -> malformed "throw" <| thunkList m

let private Current cont =
   let func = function
      | [expr] -> fun _ -> expr cont
      | m -> malformed "continuation application" <| thunkList m
   Function(func)

///Call/cc -- gives access to the current interpreter continuation.
let CallCC (args: Thunk list) (cont: Continuation) =
   match args with
   | [callee] ->
        callee (fun func ->
            match func with
            | Function(callee) -> callee [constant <| Current(cont)] cont
            | m -> malformed "call/cc" m)
   | m -> malformed "call/cc" <| thunkList m

let Apply = function
   | [arg1; arg2] as args ->
        cps {
            let! func = arg1
            let! fargs = arg2
            match func, fargs with
            | Function(f), Data(args) -> 
                let! list = toList args
                return! f list
            | _ -> return malformed "apply" <| thunkList args }
   | m -> malformed "apply" <| thunkList m

let Identity = function
   | [e] -> e
   | m   -> cps { return malformed "identity" <| thunkList m }