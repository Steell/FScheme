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

let private wrap x _ = cps { return x }

///A basic compiler
let rec private compile (compenv : CompilerEnv) expr : Environment -> Thunk =
    let compile' = compile compenv
    match expr with
    //Objects are passed as their Expression equivalent
    | Number_E(n)    -> wrap <| Number(n)
    | String_E(s)    -> wrap <| String(s)
    | Function_E(f)  -> wrap <| Function(f)
    | Container_E(o) -> wrap <| Container(o)
    | Value_E(v)     -> wrap v

    //Identifiers
    | Id(id) ->
        match findInEnv id compenv.Value with
        //If the identifier is in the compiler environment (name registry),
        //then we fetch it from the environment at runtime.
        | Some(i1, i2) -> fun env -> (env.Value.Item i1).Value.[i2].Value
        //If it's not there, then it's a free identifier.
        | None         -> failwith <| sprintf "Unbound identifier: %s" id

    //Set!
    | SetId(id, expr) ->
        match findInEnv id compenv.Value with
        //If the identifier is in the compiler environment...
        | Some(i1, i2) ->
            ///Compiled sub-expression
            let ce = compile' expr
            //At runtime we...
            fun env ->
                //Store the result of the expression in the identifier's box
                (env.Value.Item i1).Value.[i2] := make_thunk <| ce env
                //And return a dummy
                cps { return Dummy(sprintf "set! %s" id) }
        //If it's not there, then it's a free identifier.
        | None -> failwith <| sprintf "Unbound identifier: %s" id

    //Lets are really just anonymous function calls.
    | Let(names, exprs, body) -> compile' (List_E(Fun(List.map Normal names, body) :: exprs))

    //Recursive let, all identifiers must be added to the environment before any binding expressions are evaluated.
    | LetRec(names, exprs, body) ->
        ///Environment containing recursive bindings
        let compenv' = ref <| names :: compenv.Value
        ///Compiled body
        let cbody = compile compenv' body
        ///Compiled binding expressions
        let cargs = List.map (compile compenv') exprs
        ///Runtime identifier boxes
        let boxes : Thunk ref array = [| for _ in cargs -> ref <| cps { return Dummy("letrec") } |]
        //At runtime...
        fun env ->
            //We append the new frame to the environment
            let env' = ref <| ref boxes :: env.Value
            //We evaluate all the binding expressions and store them in their respective identifier's box.
            for (expr, box) in Seq.zip cargs boxes do box := make_thunk (expr env')
            //We evaluate the body in the new environment and return the result.
            cbody env'

    //Define mutates the current environment with new identifier bindings.
    | Define(name, body) ->
        ///Dummy value returned by define statements.
        let dummy = cps { return Dummy(sprintf "defined '%s'" name) }
        match List.tryFindIndex ((=) name) compenv.Value.Head with
        //If the identifier being defined is already in the environment, replace it with the new binding.
        | Some(idx) ->
            let cbody = compile' body
            fun env ->
                env.Value.Head.Value.[idx] := cbody env
                dummy
        //If it's not there, then we need to add it.
        | None ->
            ///The index of the new identifier box in the mutated environment.
            let lastindex = compenv.Value.Head.Length
            //Update the compiler environment.
            compenv := (compenv.Value.Head @ [name]) :: compenv.Value.Tail
            ///Compiled binding expression.
            let cbody = compile compenv body
            ///Dummy value for undefined identifiers.
            let dummy' = Dummy(sprintf "define '%s'" name)
            //At runtime...
            fun env ->
                ///New identifier's box
                let def = ref <| cps { return dummy' }
                //Resize the environment to accomodate the new identifier
                System.Array.Resize(env.Value.Head, lastindex + 1)
                //Place the box in the environment
                env.Value.Head.Value.SetValue(def, lastindex)
                //Evaluate the binding expression with the mutated environment
                def := make_thunk <| cbody env
                //Return the dummy for the define statement
                dummy

    //Functions
    | Fun(parameters, body) ->
        ///Traverses a syntax tree looking for new identifiers from define statements.
        let findAllDefs = function
            | Begin(exprs) ->
                let rec pred defacc = function
                    | h :: t ->
                        match h with
                        | Define(name, _) -> pred (name :: defacc) t
                        | Begin(exprs)    -> pred (pred defacc exprs) t
                        | _               -> pred defacc t
                    | [] -> List.rev defacc
                pred [] exprs
            | Define(name, _) -> [name]
            | _               -> []
        ///All identifiers being defined in the function's body.
        let defs = findAllDefs body
        ///Utility to extract the name of the given parameter.
        let paramToString = function Normal(s) | Tail(s) -> s
        ///Compiler environment containing the parameter names
        let compenv' = ref <| (defs @ List.map paramToString parameters) :: compenv.Value
        ///Compiled function body
        let cbody = compile compenv' body
        ///Number of sub-definitions
        let buffer = defs.Length
        ///Size of the environment frame to be created for this function
        let framesize = parameters.Length + buffer
        ///Default value for uninitialized identifiers
        let dummy = cps { return Dummy("undefined") }
        ///Creates a new runtime environment frame from the arguments to this function
        let pack args =
            ///New frame for the function call
            let frame = Array.zeroCreate framesize
            ///Recursive helper for processing arguments
            let rec pack' idx args = function
                //If there's one parameter left and it's a Tail, then store the parameter's argument as all the arguments in a list.
                | [Tail(_)] -> frame.[idx] <- ref <| cps { return thunkList args }
                //If there are parameters left...
                | _ :: xs ->
                    match args with
                    //Reference the first arg in the list, then pack the remaining args with the remaining names.
                    | h :: t -> frame.[idx] <- ref h; pack' (idx + 1) t xs
                    //Not enough arguments.
                    | _      -> failwith <| sprintf "Arity mismatch: Cannot apply %i-arity function on %i arguments." parameters.Length args.Length
                //If there are no parameters left...
                | [] ->
                    match args with
                    //If there are also no arguments left, we're done.
                    | [] -> ()
                    //Too many arguments.
                    | _  -> failwith <| sprintf "Arity mismatch: Cannot apply %i-arity function on %i arguments." parameters.Length args.Length
            ///List of identifier boxes for parameters
            pack' buffer args parameters
            //Initialize inner-define identifiers with dummy value
            for i in 0 .. buffer - 1 do frame.[i] <- ref dummy
            //If we don't, just create a frame out of the packed arguments.
            frame
        //At runtime, we need to add the arguments to the environment and evaluate the body.
        fun env -> cps { return Function(fun exprs -> (ref <| pack exprs) :: env.Value |> ref |> cbody) }

    //Function calls
    | List_E(fun_expr :: args) ->
        ///Compiled function
        let cfun = compile' fun_expr
        ///Compiled arguments
        let cargs = List.map compile' args
        ///At runtime...
        fun env ->
            //Evaluate the function expression
            cfun env >>= function
                //If it's a function, then evaluate the arguments and apply the function.
                | Function(f) -> f <| List.map (fun x -> x env) cargs
                //Can't call something that's not a function
                | _           -> printExpression "" expr |> sprintf "expected function for call: %s" |> failwith
                
    //Conditionals
    | If(cond, then_expr, else_expr) ->
        ///Compiled test
        let ccond = compile' cond
        ///Compiled then branch
        let cthen = compile' then_expr
        ///Compiled else branch
        let celse = compile' else_expr
        //At runtime, evaluate the expression and select the correct branch
        fun env -> ccond env ||> ValueToBool >>= function true -> cthen env | _ -> celse env

    //An empty begin statement is valid, but returns a dummy
    | Begin([]) -> wrap <| Dummy("empty begin")
    
    //A begin statement with one sub-expression is the same as just the sub-expression.
    | Begin([expr]) -> compile' expr

    //Expression sequences
    | Begin(exprs) ->
        ///Merges all nested begin expressions
        let merge =
            let rec merge' a = function
               | [Begin([]) as e]   -> merge' (compile' e :: a) []
               | Begin(exprs') :: t -> merge' (merge' a exprs') t
               | h :: t             -> merge' (compile' h :: a) t
               | []                 -> a
            merge' [] >> List.rev
        ///Compiled expressions
        let body = merge exprs
        ///Dummy value for empty begin statements
        let d = Dummy("empty begin")
        //At runtime, evaluate all expressions in the body and return the result of the last one.
        fun env -> List.map ((|>) env) body |> sequence ||> function [] -> d | l -> List.last l
        
    //Code quotations
    | Quote(syn) -> makeQuote false compenv syn
    | Quasi(syn) -> makeQuote true compenv syn

    | m -> failwith "Malformed Value"

and private makeQuote isQuasi compenv syn =
   let makeQuote' = makeQuote isQuasi compenv
   match syn with
   | Number_S(n) -> fun _ -> cps { return Number(n) }
   | String_S(s) -> fun _ -> cps { return String(s) }
   | Symbol_S(s) -> fun _ -> cps { return Symbol(s) }
   | Func_S(f)   -> fun _ -> cps { return Function(f) }

   | List_S(Symbol_S("unquote") :: t) when isQuasi ->
      match t with
      | [expr] -> syntaxToExpression macroEnv expr |> compile compenv
      | _ -> failwith "malformed 'unquote'"

   | List_S(exprs) ->
      let qargs = List.map makeQuote' exprs
      fun env ->
         cps {
            let! vals = List.map ((|>) env) qargs |> sequence
            return valList vals }

///Eval construct -- evaluates code quotations
and Eval (args: Thunk list) : Continuation -> Value =
   let rec toSyntax = function
      | Symbol(s) -> cps { return Symbol_S(s) }
      | Number(n) -> cps { return Number_S(n) }
      | String(s) -> cps { return String_S(s) }
      | Function(f) -> cps { return Func_S(f) }
      | Data(l) ->
            cps {
                let! thunks = toList l
                let! values = sequence thunks
                let! syntax = List.map toSyntax values |> sequence 
                return List_S(syntax) }
      | m -> malformed "eval" m
   match args with
   | [arg] -> 
        cps {
            let! value = arg
            let! syn = toSyntax value
            return!
                syntaxToExpression macroEnv syn
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
   AddDefaultBinding "empty" (Data(nil))
   AddDefaultBinding "null" (Data(nil))
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

let Evaluate expr = compile compileEnvironment expr environment |> force

///Parses and evaluates a Value given in text form, and returns the resulting Value
let ParseText text = 
   List.ofSeq text 
   |> parse 
   |> Begin 
   |> Evaluate

let private evaluateSchemeDefs() =
    "
   (define not (λ (x) (if x #f #t)))

   (define xor 
      (λ (a b) 
         (and (or a b) 
               (not (and a b)))))

   (define foldr 
      ;; foldr :: (X Y -> Y) Y [listof X] -> Y
      (λ (f a xs) 
         (if (empty? xs) 
             a 
             (f (first xs)
                (foldr f a (rest xs))))))
                
   (define foldl
      (λ (f a xs)
         (if (empty? xs)
             a
             (foldl f (f (first xs) a) (rest xs))))) 

   (define map
      ;; map :: (X -> Y) [listof X] -> [listof Y] 
      (λ (f xs) 
         (if (empty? xs)
             empty
             (cons (f (first xs))
                   (map f (rest xs))))))

   (define filter 
      ;; filter :: (X -> bool) [listof X] -> [listof X]
      (λ (p xs) 
         (if (empty? xs)
             empty
             (let ((frst (first xs))
                   (rst (filter p (rest xs))))
                (if (p frst)
                    (cons frst rst)
                    rst)))))

   (define cartesian-product 
      ;; cartesian-product :: (X Y ... Z -> A) [listof X] [listof Y] ... [listof Z] -> [listof A]
      (λ (comb lsts)
         (letrec ((cp-atom-list (λ (at lst) 
                                    (letrec ((cal* (λ (x l a) 
                                                      (if (empty? l) 
                                                            (reverse a) 
                                                            (cal* x (rest l) (cons (cons x (first l)) a)))))) 
                                       (cal* at lst empty))))

                  (cp-list-list (λ (l1 l2)
                                    (letrec ((cll* (λ (m n a) 
                                                      (if (or (empty? m) (empty? n))
                                                            a 
                                                            (cll* (rest m) n (append a (cp-atom-list (first m) n)))))))
                                       (cll* l1 l2 empty)))))

            (let* ((lofls (reverse lsts)) 
                     (rst (rest lofls))
                     (cp (λ (lsts) 
                           (foldl cp-list-list 
                                 (map list (first lofls))
                                 rst))))
               (map (λ (args) (apply comb args)) (cp lofls))))))

   (define qs 
      ;; qs :: [listof X] (X -> Y) (Y Y -> bool) -> [listof X]
      (λ (lst f c) 
         (if (empty? lst) 
               empty 
               (let* ((pivot (f (first lst))) 
                     (lt (filter (λ (x) (c (f x) pivot)) (rest lst)))
                     (gt (filter (λ (x) (not (c (f x) pivot))) (rest lst))))
               (append (qs lt f c) (cons (first lst) (qs gt f c))))))) 
            
   (define sort-with 
      ;; sort-with :: [listof X] (X X -> int) -> [listof X]
      (λ (lst comp) 
         (qs lst 
               (λ (x) x)
               (λ (a b) (< (comp a b) 0))))) 
                      
   (define sort-by
      ;; sort-by :: [listof X] (X -> IComparable) -> [listof X]
      (λ (lst proj) 
         (map (λ (x) (first x))                       ;; Convert back to original list
              (qs (map (λ (x) (list x (proj x))) lst) ;; Sort list of original element/projection pairs
                  (λ (y) (first (rest y)))            ;; Sort based on the second element in the sub-lists
                  <))))                                    ;; Compare using less-than

  (define zip
      ;; zip :: [listof X] [listof Y] ... [listof Z] -> [listof [listof X Y ... Z]]
      (λ (lofls) 
         (letrec ((zip'' (λ (lofls a al) 
                           (if (empty? lofls) 
                                 (list (reverse a) (reverse al)) 
                                 (if (empty? (first lofls)) 
                                    (list empty al) 
                                    (zip'' (rest lofls) 
                                           (cons (first (first lofls)) a) 
                                           (cons (rest (first lofls)) al)))))) 
                  (zip' (λ (lofls acc) 
                           (let ((result (zip'' lofls empty empty))) 
                              (if (empty? (first result)) 
                                    (reverse acc) 
                                    (let ((p (first result)) 
                                          (t (first (rest result)))) 
                                    (zip' t (cons p acc)))))))) 
            (zip' lofls empty))))

   (define combine 
      ;; combine :: (X Y ... Z -> A) [listof X] [listof Y] ... [listof Z] -> [listof A]
      (λ (f lofls) 
         (map (λ (x) (apply f x)) 
               (zip lofls))))

  (define for-each 
     ;; for-each :: (X -> unit) [listof X] -> unit
     (λ (f lst) (foldr (λ (x _) (f x)) (begin) lst)))
  
  (define fix (λ (f) (f (fix f))))
  "
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
   case "(let ((y 6)) (let ((f (λ (x) (+ x y)))) (let ((y 5)) (f 4))))" "10"

   //Apply
   case "(apply + '(1 2))" "3"
   case "(apply append '((1) (2)))" "(1 2)"
   
   //Fold
   case "(foldr + 0 '(1 2 3))"   "6"
   case "(foldr * 1 '(2 3 4 5))" "120" // fold
   
   //Map
   case "(map (λ (x) x) '(1 2 3))" "(1 2 3)"
   
   //Filter
   case "(filter (λ (x) (< x 2)) '(0 2 3 4 1 6 5))" "(0 1)"
   
   //Cartesian Product
   case "(cartesian-product list (list 1 2) (list 3 4) (list 5 6))" 
        "((1 3 5) (1 3 6) (1 4 5) (1 4 6) (2 3 5) (2 3 6) (2 4 5) (2 4 6))"
   
   //Sorting
   case "(sort-by '((2 2) (2 1) (1 1)) (λ (x) (foldr + 0 x)))" "((1 1) (2 1) (2 2))"
   case "(sort-with '((2 2) (2 1) (1 1)) (λ (x y) (let ((size (λ (l) (foldr + 0 l)))) (- (size x) (size y)))))" "((1 1) (2 1) (2 2))"
   
   //Zip/Combine
   case "(zip '((1) (2) (3)) '((4) (5) (6)))" "(((1) (4)) ((2) (5)) ((3) (6)))"
   case "(combine (λ (x y) (append x y)) '((1) (2) (3)) '((4) (5) (6)))" "((1 4) (2 5) (3 6))"
   
   //Engine Tests
   case "(quote (* 2 3))" "(* 2 3)" // quote primitive
   case "(eval '(* 2 3))" "6" // eval quoted Value
   case "(quote (* 2 (- 5 2)))" "(* 2 (- 5 2))" // quote nested
   case "(quote (* 2 (unquote (- 5 2))))" "(* 2 (unquote (- 5 2)))" // quote nested unquote
   case "(quasiquote (* 2 (unquote (- 5 2))))" "(* 2 3)" // quote nested unquote
   case "(let ((a 1)) (begin (set! a 2) a))" "2" // begin and assign
   case "(let* ((a 5) (dummy (set! a 10))) a)" "10" // re-assign after let
   case "(begin (define too-many (λ (a x) x)) (too-many 1 2 3))" "(2 3)"
   case "(too-many '(1 1) '(2 2) '(3 3))" "((2 2) (3 3))"
   case "(reverse '(1 2 3))" "(3 2 1)" // reverse
   case "(list 1 2 3)" "(1 2 3)"
   case "(let ((square (λ (x) (* x x)))) (map square '(1 2 3 4 5 6 7 8 9)))" "(1 4 9 16 25 36 49 64 81)" // mapping
   case "(let ((square (λ (x) (* x x)))) (map square '(9)))" "(81)" // mapping single
   case "(let ((square (λ (x) (* x x)))) (map square '()))" "()" // mapping empty
   case "(call/cc (λ (c) (c 10)))" "10" // super-simple call/cc
   case "(call/cc (λ (c) (if (c 10) 20 30)))" "10" // call/cc bailing out of 'if'
   case "(+ 8 (call/cc (λ (k^) (* (k^ 5) 100))))" "13" // call/cc bailing out of multiplication
   case "(* (+ (call/cc (λ (k^) (/ (k^ 5) 4))) 8) 3)" "39" // call/cc nesting
   case "(let ((divide (λ (x y) (call/cc (λ (k^) (if (= y 0) (k^ \"error\") (/ x y))))))) (divide 1 0))" "\"error\"" // call/cc as an error handler

   //Lazy Test
   case "((λ (x y) x) 1 ((λ (x) (x x)) (λ (x) (x x))))" "1"
   case "(let ((nats (cons 0 (map add1 nats)))) (take 5 nats))" "(0 1 2 3 4)"

   success.Value

let runTests() = 
   if (ErrorLog(System.Console.WriteLine) |> test) then 
      System.Console.WriteLine("All Tests Passed.")
