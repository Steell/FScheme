module FScheme.Interpreter
#light

//An F# Scheme Interpreter

open FScheme.Library
open FScheme.Parser
open FScheme.Thunk
open FScheme.Value
open FScheme.Value.List

open ExtCore.Collections
open System.Numerics
open System.IO


type Frame = Thunk ref [] ref
type Environment = Frame list ref

type private CompilerFrame = string list
type private CompilerEnv = CompilerFrame list ref

let private findInEnv (name : string) compenv =
   let rec find acc = function
      | h :: t ->
         match List.tryFindIndex ((=) name) h with
         | Some(i) -> Some(acc, i)
         | None -> find (acc + 1) t
      | [] -> None
   find 0 compenv

///A basic compiler
let rec private compile (compenv : CompilerEnv) syntax : Environment -> Thunk =
   let compile' = compile compenv
   match syntax with
   | Number_S(n) ->
      let x = Number(n)
      fun _ -> cps { return x }

   | String_S(s) ->
      let x = String(s)
      fun _ -> cps { return x }

   | Func_S(f) ->
      let x = Function(f)
      fun _ -> cps { return x }

   | Id(id) ->
      match findInEnv id compenv.Value with
      | Some(i1, i2) -> fun env -> (env.Value.Item i1).Value.[i2].Value
      | None -> sprintf "Unbound identifier: %s" id |> failwith

   | SetId(id, expr) ->
      let ce = compile' expr
      match findInEnv id compenv.Value with
      | Some(i1, i2) -> 
         fun env ->
            let box = (env.Value.Item i1).Value.[i2]
            box := make_thunk (ce env)
            constant <| Dummy(sprintf "set! %s" id)
      | None -> sprintf "Unbound identifier: %s" id |> failwith

   | Bind(names, exprs, body) -> compile' (List_S(Fun(names, body) :: exprs))

   | BindRec(names, exprs, body) ->
      let cbody = compile (ref (names :: compenv.Value)) body
      let cargs = List.map (ref (names :: compenv.Value) |> compile) exprs
      let boxes = [ for _ in 1 .. List.length cargs -> Dummy("letrec") |> constant |> ref ]
      let newFrame : Frame = List.toArray boxes |> ref
      fun env ->
         let env' = newFrame :: env.Value |> ref
         let rec mapbind = function
            | (expr, box) :: t -> box := make_thunk (expr env'); mapbind t
            | [] -> cbody env'
         List.zip cargs boxes |> mapbind

   | Define(name, body) ->
      match List.tryFindIndex ((=) name) compenv.Value.Head with
      | Some(idx) ->
         let cbody = compile' body
         fun env ->
            let box = env.Value.Head.Value.[idx]
            box := make_thunk (cbody env)
            constant <| Dummy(sprintf "defined '%s'" name)
      | None ->
         let lastindex = compenv.Value.Head.Length
         compenv := (List.append compenv.Value.Head [name]) :: compenv.Value.Tail
         let cbody = compile compenv body
         fun env -> 
           let def : Thunk ref = Dummy(sprintf "define '%s'" name) |> constant |> ref
           System.Array.Resize(env.Value.Head, env.Value.Head.Value.Length + 1)
           env.Value.Head.Value.SetValue(def, lastindex)
           def := make_thunk (cbody env)
           constant <| Dummy(sprintf "defined '%s'" name)

   | Fun(names, body) ->
      let compenv' = names :: compenv.Value |> ref
      let cbody = compile compenv' body
      let amt = List.length names
      let pack (args: Thunk list) =
         let arglen = List.length args
         if arglen = amt then
            Seq.map ref args |> Seq.toArray
         elif amt > 0 then
            Seq.append (Seq.take (amt - 1) args) 
                       (Seq.skip (amt - 1) args |> Seq.toList |> thunkList |> constant |> Seq.singleton)
            |> Seq.map ref 
            |> Seq.toArray
         else
            failwith "Can't call 0-arity function with arguments."
      fun env ->
         Function(fun exprs -> ref (pack exprs) :: env.Value |> ref |> cbody) |> constant

   | List_S(fun_expr :: args) ->
      let cfun = compile' fun_expr
      let cargs = List.map compile' args
      fun env cont ->
         let cont' = function
            | Function(f) ->
                f (List.map (fun carg -> make_thunk (carg env)) cargs) cont
            | m -> printSyntax "" syntax |> sprintf "expected function for call: %s" |> failwith
         cfun env cont'

   | If(cond, then_expr, else_expr) ->
      let ccond = compile' cond
      let cthen = compile' then_expr
      let celse = compile' else_expr
      fun env cont ->
         let cont' = function
            | Bool(b) -> (if b then cthen else celse) env cont
            | _ -> cthen env cont
         ccond env cont' 

   | Begin([expr]) -> compile' expr

   | Begin(exprs) ->
      let body = List.map compile' exprs
      let d = Dummy("empty begin")
      fun env cont ->
         let rec runall' acc = function
            | h :: t -> h env <| flip runall' t
            | [] -> acc |> cont
         runall' d body

   | Quote_S(parser) -> makeQuote false compenv parser
   | Quasi_S(parser) -> makeQuote true compenv parser

   | m -> failwith "Malformed Value"

and private makeQuote isQuasi compenv parser =
   let makeQuote' = makeQuote isQuasi compenv
   match parser with
   | Number_P(n) -> fun _ -> cps { return Number(n) }
   | String_P(s) -> fun _ -> cps { return String(s) }
   | Symbol_P(s) -> fun _ -> cps { return Symbol(s) }
   | Func_P(f)   -> fun _ -> cps { return Function(f) }

   | List_P(Symbol_P("unquote") :: t) when isQuasi ->
      match t with
      | [expr] -> parserToSyntax macroEnv expr |> compile compenv
      | _ -> failwith "malformed 'unquote'"

   | List_P(exprs) ->
      let qargs = List.map makeQuote' exprs
      fun env cont ->
         let rec mapquote acc = function
            | h :: t -> h env <| (fun x -> mapquote (x :: acc) t)
            | [] -> List.rev acc |> List.map constant |> thunkList |> cont
         mapquote [] qargs

///Eval construct -- evaluates code quotations
and Eval (args: Thunk list) : Continuation -> Value =
   let rec toParser = function
      | Symbol(s) -> cps { return Symbol_P(s) }
      | Number(n) -> cps { return Number_P(n) }
      | String(s) -> cps { return String_P(s) }
      | Function(f) -> cps { return Func_P(f) }
      | Data(l) -> 
            let rec mapparse acc = function
                | [] -> cps { return List.rev acc |> List_P }
                | h :: t ->
                    cps {
                        let! x = h
                        let! parser = toParser x
                        return! mapparse (parser :: acc) t }
            cps {
                let! l = toList l
                return! mapparse [] l }
      | m -> malformed "eval" m
   match args with
   | [arg] -> 
        cps {
            let! value = arg
            let! parser = toParser value
            return!
                parserToSyntax macroEnv parser
                    |> compile compileEnvironment
                    |> fun x -> x environment }
   | m -> cps { return malformed "eval" <| thunkList m }


///Load construct -- loads library files, reads them using the simple tokenizer and parser.
and load file = Load [constant <| String(file)] (fun _ -> Dummy("")) |> ignore
and Load : Func = function
   | [s] ->
      cps {
        let! file = s
        match file with
        | String(file) -> 
            (File.OpenText(file)).ReadToEnd() 
                 |> List.ofSeq 
                 |> parse
                 |> List.iter (fun x -> compile compileEnvironment x environment (fun _ -> Dummy("Dummy 'load'")) |> ignore);
            return Dummy(sprintf "Loaded '%s'." file)
        | m -> return malformed "load" m
      }
   | m -> malformed "load" <| thunkList m

and compileEnvironment : CompilerEnv =
   [[]] |> ref
///Our base environment
and environment : Environment =
   [[||] |> ref ] |> ref

let mutable private tempEnv : (string * Thunk ref) list = []
let AddDefaultBinding name expr =
   tempEnv <- (name, ref <| constant expr) :: tempEnv

let private makeEnvironments() =
   AddDefaultBinding "empty" nil
   AddDefaultBinding "null" nil
   AddDefaultBinding "#t" (Bool(true))
   AddDefaultBinding "#f" (Bool(false))
   AddDefaultBinding "display" (Function(Display))
   AddDefaultBinding "*" (Function(Multiply))
   AddDefaultBinding "/" (Function(Divide))
   AddDefaultBinding "%" (Function(Modulus))
   AddDefaultBinding "+" (Function(Add))
   AddDefaultBinding "-" (Function(Subtract))
   AddDefaultBinding "pow" (Function(Exponent))
   AddDefaultBinding "<=" (Function(LTE))
   AddDefaultBinding ">=" (Function(GTE))
   AddDefaultBinding "<" (Function(LT))
   AddDefaultBinding ">" (Function(GT))
   AddDefaultBinding "=" (Function(EQ))
   AddDefaultBinding "add1" (Function(Add1))
   AddDefaultBinding "sub1" (Function(Sub1))
   AddDefaultBinding "cons" (Function(FScheme.Library.Cons))
   AddDefaultBinding "car" (Function(Car))
   AddDefaultBinding "first" (Function(Car))
   AddDefaultBinding "cdr" (Function(Cdr))
   AddDefaultBinding "rest" (Function(Cdr))
   AddDefaultBinding "len" (Function(Len))
   AddDefaultBinding "length" (Function(Len))
   AddDefaultBinding "append" (Function(Append))
   AddDefaultBinding "take" (Function(Take))
   AddDefaultBinding "get" (Function(Get))
   AddDefaultBinding "drop" (Function(Drop))
   AddDefaultBinding "build-seq" (Function(BuildSeq))
   AddDefaultBinding "load" (Function(Load))
   AddDefaultBinding "call/cc" (Function(CallCC))
   AddDefaultBinding "empty?" (Function(IsEmpty))
   AddDefaultBinding "reverse" (Function(Rev))
   AddDefaultBinding "rev" (Function(Rev))
   AddDefaultBinding "list" (Function(MakeList))
   AddDefaultBinding "sort" (Function(Sort))
   AddDefaultBinding "throw" (Function(Throw))
   AddDefaultBinding "rand" (Function(RandomDbl))
   AddDefaultBinding "string->num" (Function(String2Num))
   AddDefaultBinding "num->string"(Function(Num2String))
   AddDefaultBinding "concat-strings" (Function(Concat))
   AddDefaultBinding "eval" (Function(Eval))
   AddDefaultBinding "apply" (Function(Apply))
   AddDefaultBinding "identity" (Function(Identity))

let Evaluate syntax = compile compileEnvironment syntax environment |> force

///Parses and evaluates a Value given in text form, and returns the resulting Value
let ParseText text = 
   List.ofSeq text 
   |> parse 
   |> Begin 
   |> Evaluate

let private evaluateSchemeDefs() =
    "
   (define not (lambda (x) (if x #f #t)))

   (define xor 
      (lambda (a b) 
         (and (or a b) 
               (not (and a b)))))

   (define fold 
      ;; fold :: (X Y -> Y) Y [listof X] -> Y
      (lambda (f a xs) 
         (if (empty? xs) 
             a 
             (f (first xs)
                (fold f a (rest xs)))))) 

   (define map
      ;; map :: (X -> Y) [listof X] -> [listof Y] 
      (lambda (f xs) 
         (if (empty? xs)
             empty
             (cons (f (first xs))
                   (map f (rest xs))))))

   (define filter 
      ;; filter :: (X -> bool) [listof X] -> [listof X]
      (lambda (p xs) 
         (if (empty? xs)
             empty
             (let ((frst (first xs))
                   (rst (filter p (rest xs))))
                (if (p frst)
                    (cons frst rst)
                    rst)))))

   (define cartesian-product 
      ;; cartesian-product :: (X Y ... Z -> A) [listof X] [listof Y] ... [listof Z] -> [listof A]
      (lambda (comb lsts)
         (letrec ((cp-atom-list (lambda (at lst) 
                                    (letrec ((cal* (lambda (x l a) 
                                                      (if (empty? l) 
                                                            (reverse a) 
                                                            (cal* x (rest l) (cons (cons x (first l)) a)))))) 
                                       (cal* at lst empty))))

                  (cp-list-list (lambda (l1 l2)
                                    (letrec ((cll* (lambda (m n a) 
                                                      (if (or (empty? m) (empty? n))
                                                            a 
                                                            (cll* (rest m) n (append a (cp-atom-list (first m) n)))))))
                                       (cll* l1 l2 empty)))))

            (let* ((lofls (reverse lsts)) 
                     (rst (rest lofls))
                     (cp (lambda (lsts) 
                           (fold cp-list-list 
                                 (map list (first lofls))
                                 rst))))
               (map (lambda (args) (apply comb args)) (cp lofls))))))

   (define qs 
      ;; qs :: [listof X] (X -> Y) (Y Y -> bool) -> [listof X]
      (lambda (lst f c) 
         (if (empty? lst) 
               empty 
               (let* ((pivot (f (first lst))) 
                     (lt (filter (lambda (x) (c (f x) pivot)) (rest lst)))
                     (gt (filter (lambda (x) (not (c (f x) pivot))) (rest lst))))
               (append (qs lt f c) (cons (first lst) (qs gt f c))))))) 
            
   (define sort-with 
      ;; sort-with :: [listof X] (X X -> int) -> [listof X]
      (lambda (lst comp) 
         (qs lst 
               (lambda (x) x)
               (lambda (a b) (< (comp a b) 0))))) 
                      
   (define sort-by
      ;; sort-by :: [listof X] (X -> IComparable) -> [listof X]
      (lambda (lst proj) 
         (map (lambda (x) (first x))                       ;; Convert back to original list
              (qs (map (lambda (x) (list x (proj x))) lst) ;; Sort list of original element/projection pairs
                  (lambda (y) (first (rest y)))            ;; Sort based on the second element in the sub-lists
                  <))))                                    ;; Compare using less-than

  (define zip
      ;; zip :: [listof X] [listof Y] ... [listof Z] -> [listof [listof X Y ... Z]]
      (lambda (lofls) 
         (letrec ((zip'' (lambda (lofls a al) 
                           (if (empty? lofls) 
                                 (list (reverse a) (reverse al)) 
                                 (if (empty? (first lofls)) 
                                    (list empty al) 
                                    (zip'' (rest lofls) 
                                           (cons (first (first lofls)) a) 
                                           (cons (rest (first lofls)) al)))))) 
                  (zip' (lambda (lofls acc) 
                           (let ((result (zip'' lofls empty empty))) 
                              (if (empty? (first result)) 
                                    (reverse acc) 
                                    (let ((p (first result)) 
                                          (t (first (rest result)))) 
                                    (zip' t (cons p acc)))))))) 
            (zip' lofls empty))))

   (define combine 
      ;; combine :: (X Y ... Z -> A) [listof X] [listof Y] ... [listof Z] -> [listof A]
      (lambda (f lofls) 
         (map (lambda (x) (apply f x)) 
               (zip lofls))))

  (define for-each 
     ;; for-each :: (X -> unit) [listof X] -> unit
     (lambda (f lst) (fold (lambda (x _) (f x)) (begin) lst)))
  
  (define fix (lambda (f) (f (fix f))))
  
  (define nats (cons 0 (map add1 nats)))"
    |> ParseText |> ignore

makeEnvironments()
environment := [Seq.map (fun (_, x) -> x) tempEnv |> Seq.toArray |> ref]
compileEnvironment := [List.map (fun (x, _) -> x) tempEnv]
evaluateSchemeDefs()

///REP -- Read/Eval/Prints
let rep = ParseText >> print

///REPL -- Read/Eval/Print Loop
let repl() : unit =
   let rec repl' output =
      printf "%s\n> " output
      try System.Console.ReadLine() |> rep |> repl'
      with ex -> repl' ex.Message
   repl' ""

type ErrorLog = delegate of string -> unit

//Tests
let test (log : ErrorLog) =
   let success = ref true
   let case source expected =
      try
         //printfn "TEST: %s" source
         let output = rep source
         //Console.WriteLine(sprintf "TESTING: %s" source)
         if output <> expected then
            success := false
            sprintf "TEST FAILED: %s [Expected: %s, Actual: %s]" source expected output |> log.Invoke
      with ex ->
         success := false 
         sprintf "TEST CRASHED: %s [%s]" ex.Message source |> log.Invoke
   
   //Not
   case "(not #t)" "#f"
   case "(not #f)" "#t"
   
   //And
   case "(and #f #f)" "#f" // or (false)
   case "(and #t #f)" "#f" // or (false)
   case "(and #f #t)" "#f" // or (false)
   case "(and #t #t)" "#t" // or (true)
   
   //Or
   case "(or #f #f)" "#f" // or (false)
   case "(or #t #f)" "#t" // or (true)
   case "(or #f #t)" "#t" // or (true)
   case "(or #t #t)" "#t" // or (true)

   //Xor
   case "(xor #f #f)" "#f" // xor (false)
   case "(xor #t #f)" "#t" // xor (true)
   case "(xor #f #t)" "#t" // xor (true)
   case "(xor #t #t)" "#f" // xor (false)
   
   //Built-in Tests
   case "(cons 1 (cons 5 (cons \"hello\" empty)))" "(1 5 \"hello\")" // cons and empty
   case "(car (list 5 6 2))" "5" // car / first
   case "(cdr (list 5 6 2))" "(6 2)" // cdr / rest
   case "(len (list 5 6 2))" "3" // len
   case "(append '(1 2 3) '(4 5 6))" "(1 2 3 4 5 6)" // append
   case "(take 2 '(1 2 3))" "(1 2)" // take
   case "(get 2 '(1 2 3))" "3" // get
   case "(drop 2 '(1 2 3))" "(3)" // drop
   case "(build-seq 0 10 1)" "(0 1 2 3 4 5 6 7 8 9 10)" // build-seq
   case "(reverse '(1 2 3))" "(3 2 1)" // reverse
   case "(empty? '())" "#t" // empty?
   case "(empty? '(1))" "#f" // empty?
   case "(sort '(8 4 7 6 1 0 2 9))" "(0 1 2 4 6 7 8 9)" // sort
   case "(sort (list \"b\" \"c\" \"a\"))" "(\"a\" \"b\" \"c\")" // sort

   //Scope
   case "(let ((y 6)) (let ((f (lambda (x) (+ x y)))) (let ((y 5)) (f 4))))" "10"

   //Apply
   case "(apply + '(1 2))" "3"
   case "(apply append '((1) (2)))" "(1 2)"
   
   //Fold
   case "(fold + 0 '(1 2 3))"   "6"
   case "(fold * 1 '(2 3 4 5))" "120" // fold
   
   //Map
   case "(map (lambda (x) x) '(1 2 3))" "(1 2 3)"
   
   //Filter
   case "(filter (lambda (x) (< x 2)) '(0 2 3 4 1 6 5))" "(0 1)"
   
   //Cartesian Product
   //case "(cartesian-product list (list 1 2) (list 3 4) (list 5 6))" 
   //     "((1 3 5) (1 3 6) (1 4 5) (1 4 6) (2 3 5) (2 3 6) (2 4 5) (2 4 6))"
   
   //Sorting
   case "(sort-by '((2 2) (2 1) (1 1)) (lambda (x) (fold + 0 x)))" "((1 1) (2 1) (2 2))"
   case "(sort-with '((2 2) (2 1) (1 1)) (lambda (x y) (let ((size (lambda (l) (fold + 0 l)))) (- (size x) (size y)))))" "((1 1) (2 1) (2 2))"
   
   //Zip/Combine
   case "(zip '((1) (2) (3)) '((4) (5) (6)))" "(((1) (4)) ((2) (5)) ((3) (6)))"
   case "(combine (lambda (x y) (append x y)) '((1) (2) (3)) '((4) (5) (6)))" "((1 4) (2 5) (3 6))"
   
   //Engine Tests
   case "(quote (* 2 3))" "(* 2 3)" // quote primitive
   case "(eval '(* 2 3))" "6" // eval quoted Value
   case "(quote (* 2 (- 5 2)))" "(* 2 (- 5 2))" // quote nested
   case "(quote (* 2 (unquote (- 5 2))))" "(* 2 (unquote (- 5 2)))" // quote nested unquote
   case "(quasiquote (* 2 (unquote (- 5 2))))" "(* 2 3)" // quote nested unquote
   case "(let ((a 1)) (begin (set! a 2) a))" "2" // begin and assign
   case "(let* ((a 5) (dummy (set! a 10))) a)" "10" // re-assign after let
   case "(begin (define too-many (lambda (a x) x)) (too-many 1 2 3))" "(2 3)"
   case "(too-many '(1 1) '(2 2) '(3 3))" "((2 2) (3 3))"
   case "(reverse '(1 2 3))" "(3 2 1)" // reverse
   case "(list 1 2 3)" "(1 2 3)"
   case "(let ((square (lambda (x) (* x x)))) (map square '(1 2 3 4 5 6 7 8 9)))" "(1 4 9 16 25 36 49 64 81)" // mapping
   case "(let ((square (lambda (x) (* x x)))) (map square '(9)))" "(81)" // mapping single
   case "(let ((square (lambda (x) (* x x)))) (map square '()))" "()" // mapping empty
   case "(call/cc (lambda (c) (c 10)))" "10" // super-simple call/cc
   case "(call/cc (lambda (c) (if (c 10) 20 30)))" "10" // call/cc bailing out of 'if'
   case "(+ 8 (call/cc (lambda (k^) (* (k^ 5) 100))))" "13" // call/cc bailing out of multiplication
   case "(* (+ (call/cc (lambda (k^) (/ (k^ 5) 4))) 8) 3)" "39" // call/cc nesting
   case "(let ((divide (lambda (x y) (call/cc (lambda (k^) (if (= y 0) (k^ \"error\") (/ x y))))))) (divide 1 0))" "\"error\"" // call/cc as an error handler

   //Lazy Test
   case "((lambda (x y) x) 1 ((lambda (x) (x x)) (lambda (x) (x x))))" "1"
   case "(let ((nats (cons 0 (map add1 nats)))) (take 5 nats))" "(0 1 2 3 4)"

   success.Value

let runTests() = 
   if (ErrorLog(System.Console.WriteLine) |> test) then 
      System.Console.WriteLine("All Tests Passed.")
