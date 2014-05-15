module FScheme.Library

open FScheme.Parser
open FScheme.Thunk
open FScheme.Value

open ExtCore.Collections

///Prints a malformed statement error.
let malformed n e = sprintf "Malformed '%s': %s" n (print (List(LazyList.ofList [constant <| e]))) |> failwith

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
            | Number(n2) ->
                let! result = foldOp name op (op n n2) args
                return Number(result)
            | m -> return malformed (sprintf "%s arg" name) m
        | m -> return malformed (sprintf "%s arg" name) m }
   //Otherwise, fail.
   | m -> malformed name <| List(LazyList.ofList m)

let private math0 op name start exprs = 
  cps {
      let! result = foldOp name op start exprs
      return Number(result) }
  

let private math1 op (op2: Func) unary name = function
  | [arg] ->
    cps {
        let! n = arg 
        return
            match n with
            | Number(n) -> Number(unary n)
            | m -> malformed name m }
  | arg :: args ->
    cps {
        let! n = arg
        match n with
        | Number(n) ->
            let cont' x =
                match x with
                | Number x -> Number(op n x)
                | m -> malformed (sprintf "%s arg" name) m
            return op2 args cont'
        | m -> return malformed (sprintf "%s arg" name) m }
  | m -> malformed name <| List(LazyList.ofList m)

//Arithmatic functions
let Add : Func = math0 (+) "addition" 0.
let Subtract : Func = math1 (-) Add (fun x -> -x) "subtraction"
let Multiply : Func = math0 (*) "multiplication" 1.
let Divide : Func = math1 (/) Multiply ((/) 1.) "division"
let Modulus : Func = mathbin (%) "modulus"
let Exponent : Func = mathbin ( ** ) "exponent"

///Simple wrapper for comparison operations.
let private boolMath (op : (System.IComparable -> System.IComparable -> bool)) name args =
   let comp a' b' = 
      match (op a' b') with
      | true -> Number(1.0)
      | _ -> Number(0.0)
   match args with
   | [a; b] ->
       cps {
           let! a = a
           let! b = b
           return
               match a, b with
               | Number(a), Number(b) -> comp a b
               | String(a), String(b) -> comp a b
               | m -> malformed name (List(Seq.map constant [a; b] |> LazyList.ofSeq)) }
   | m -> malformed name <| List(LazyList.ofList m)

//Comparison operations.
let LTE : Func = boolMath (<=) "less-than-or-equals"
let GTE : Func = boolMath (>=) "greater-than-or-equals"
let LT : Func = boolMath (<) "less-than"
let GT : Func = boolMath (>) "greater-than"
let EQ : Func = boolMath (=) "equals"

///Display construct -- used to print to stdout
let Display = function
   | [e] ->
        cps {
            let! v = e
            print v |> printf "DISPLAY: %s \n";
            return Dummy("Dummy 'display'") }
   | m -> malformed "display" <| List(LazyList.ofList m)

let Add1 = function
   | [arg] ->
        cps {
            let! n = arg
            return
                match n with
                | Number(n) -> Number(n + 1.)
                | m -> malformed "add1" <| m }
   | m -> malformed "add1" <| List(LazyList.ofList m)

let Sub1 = function
   | [arg] ->
        cps {
            let! n = arg
            return
                match n with
                | Number(n) -> Number(n - 1.)
                | m -> malformed "aub1" <| m }
   | m -> malformed "sub1" <| List(LazyList.ofList m)

//Random Number
let private _r = new System.Random()
let RandomDbl = function
    | [] -> cps { return Number(_r.NextDouble()) }
    | m -> malformed "random" <| List(LazyList.ofList m)

//List Functions
let IsEmpty = function
    | [arg] -> 
        cps {
            let! l = arg
            match l with
            | List(s) when Seq.isEmpty s -> return Number(1.0)
            | _ -> return Number(0.0) }
    | m -> malformed "empty?" <| List(LazyList.ofList m)

let Cons = function 
    | [head; tail] -> 
        cps {
            let! t = tail
            return
                match t with
                | List(t) -> List(LazyList.cons head t)
                | _ -> malformed "cons" <| List(LazyList.ofList [head; tail]) }
    | m -> malformed "cons" <| List(LazyList.ofList m)

let Car = function 
    | [l] ->
        cps {
            let! list = l
            match list with
            | List(l) -> return! Seq.nth 0 l
            | _ -> return malformed "car" <| List(LazyList.ofList [l]) }
    | m -> malformed "car" <| List(LazyList.ofList m)

let Cdr = function
    | [l] ->
        cps {
            let! list = l
            return
                match list with
                | List(l) -> List(LazyList.tail l)
                | _ -> malformed "car" <| List(LazyList.ofList [l]) }
    | m -> malformed "cdr" <| List(LazyList.ofList m)

let Rev = function
    | [l] ->
        cps {
            let! list = l
            return
                match list with
                | List(l) -> LazyList.toList l |> List.rev |> LazyList.ofList |> List
                | m -> malformed "reverse" m }
    | m -> malformed "reverse" <| List(LazyList.ofList m)

let MakeList args = LazyList.ofList args |> List |> constant

let Len = function
    | [l] ->
        cps {
            let! list = l
            return
                match list with
                | List(l) -> Number(double (LazyList.length l))
                | m -> malformed "len" m }
    | m -> malformed "len" <| List(LazyList.ofList m)

let Append = function
    | [l1; l2] ->
        cps {
            let! list1 = l1
            let! list2 = l2
            return 
                match list1, list2 with
                | List(l1), List(l2) -> List(LazyList.append l1 l2)
                | _ -> malformed "append" (List(LazyList.ofList [l1; l2])) }
    | m -> malformed "append" <| List(LazyList.ofList m)

let Take = function
    | [n; l] ->
        cps {
            let! amt = n
            let! list = l
            return
                match amt, list with
                | Number(n), List(l) -> List(LazyList.take (int n) l)
                | _ -> malformed "take" (List(LazyList.ofList [n; l])) }
    | m -> malformed "take" <| List(LazyList.ofList m)

let Get = function
    | [n; l] ->
        cps {
            let! amt = n
            let! list = l
            match amt, list with
            | Number(n), List(l) -> return! Seq.nth (int n) l
            | _ -> return malformed "get" (List(LazyList.ofList [n; l])) }
    | m -> malformed "get" <| List(LazyList.ofList m)

let Drop = function
    | [n; l] ->
        cps {
            let! amt = n
            let! list = l
            return
                match amt, list with
                | Number(n), List(l) -> List(LazyList.skip (int n) l)
                | _ -> malformed "drop" (List(LazyList.ofList [n; l])) }
    | m -> malformed "drop" <| List(LazyList.ofList m)

///Sorts using natural ordering. Only works for primitive types (numbers, strings, etc.)
let Sort = function
   //We expect a list of Values as the only argument.
   | [l] ->
      cps {
          let! list = l
          match list with
          | List(l) ->
              if Seq.isEmpty l then
                  return malformed "sort" (List(l))
              else
                  //Peek and see what kind of data we're sorting
                  let n = Seq.nth 0 l
                  let! first = n
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
                            LazyList.map (force >> converter) l 
                                |> Seq.sort 
                                |> Seq.map (fun n -> cps { return Number(n) }) 
                                |> LazyList.ofSeq
                                |> List
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
                            LazyList.map (force >> converter) l 
                                |> Seq.sort 
                                |> Seq.map (fun n -> cps { return String(n) }) 
                                |> LazyList.ofSeq
                                |> List
                  | m -> return malformed "sort type" m
          | m ->  return malformed "sort" m }
   //Otherwise, fail.
   | m -> malformed "sort" <| List(LazyList.ofList m)

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
                        |> Seq.map (Number >> constant) 
                        |> LazyList.ofSeq 
                        |> List
                | _ -> malformed "build-seq" (List(LazyList.ofList args)) }
   | m -> malformed "build-seq" <| List(LazyList.ofList m)

let String2Num = function
    | [s] ->
        cps {
            let! string = s
            return
                match string with
                | String(s) -> Number(System.Convert.ToDouble(s))
                | m -> malformed "string" m }
    | m -> malformed "string" <| List(LazyList.ofList m)

let Num2String = function
    | [n] ->
        cps {
            let! num = n
            return
                match num with
                | Number(n) -> String(n.ToString())
                | m -> malformed "number" m }
    | m -> malformed "number" <| List(LazyList.ofList m)

let Concat = function
    | [l] ->
        cps {
            let! list = l
            match force l with
            | List(l) -> 
                let rec concat a l =
                    cps {
                        if Seq.isEmpty l then
                            return String(a)
                        else
                            let! string = Seq.nth 0 l
                            match string with
                            | String(s) -> return! concat (a + s) (Seq.skip 1 l)
                            | m -> return malformed "string" m }
                return! concat "" l
            | m -> return malformed "concat" m }
    | m -> malformed "concat" <| List(LazyList.ofList m)

///Error construct
let Throw = function
   | [s] ->
        match force s with
        | String(s) -> failwith s
        | m -> malformed "throw" m
   | m -> malformed "throw" <| List(LazyList.ofList m)

let private Current cont =
   let func = function
      | [expr] -> fun _ -> expr cont
      | m -> malformed "continuation application" <| List(LazyList.ofList m)
   Function(func)

///Call/cc -- gives access to the current interpreter continuation.
let CallCC (args: Thunk list) (cont: Continuation) =
   match args with
   | [callee] ->
        callee (fun func ->
            match func with
            | Function(callee) -> callee [constant <| Current(cont)] cont
            | m -> malformed "call/cc" m)
   | m -> malformed "call/cc" <| List(LazyList.ofList m)

let Apply = function
   | [arg1; arg2] as args ->
        cps {
            let! func = arg1
            let! fargs = arg2
            match func, fargs with
            | Function(f), List(args) -> return! f (List.ofSeq args)
            | _ -> return malformed "apply" (List(LazyList.ofList args)) }
   | m -> malformed "apply" <| List(LazyList.ofList m)

let Identity = function
   | [e] -> e
   | m   -> cps { return malformed "identity" <| List(LazyList.ofList m) }