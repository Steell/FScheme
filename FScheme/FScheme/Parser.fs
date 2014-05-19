module FScheme.Parser

open FScheme.Value

open System

//Simple Tokenizer for quickly defining Values in Scheme Expression.
type Token =
   | Open | Close
   | QuoteT | QuasiT | Unquote
   | Number of string
   | String of string
   | Symbol of string

let tokenize source =
   let rec string acc = function
      | '\\' :: '"' :: t -> string (acc + "\"") t // escaped quote becomes quote
      | '\\' :: 'b' :: t -> string (acc + "\b") t // escaped backspace
      | '\\' :: 'f' :: t -> string (acc + "\f") t // escaped formfeed
      | '\\' :: 'n' :: t -> string (acc + "\n") t // escaped newline
      | '\\' :: 'r' :: t -> string (acc + "\r") t // escaped return
      | '\\' :: 't' :: t -> string (acc + "\t") t // escaped tab
      | '\\' :: '\\' :: t -> string (acc + "\\") t // escaped backslash
      | '"' :: t -> acc, t // closing quote terminates
      | c :: t -> string (acc + (c.ToString())) t // otherwise accumulate chars
      | _ -> failwith "Malformed string."
   let rec comment = function
      | '\r' :: t | '\n' :: t -> t // terminated by line end
      | [] -> [] // or by EOF
      | _ :: t -> comment t
   let rec token acc = function
      | (')' :: _) as t -> acc, t // closing paren terminates
      | w :: t when Char.IsWhiteSpace(w) -> acc, t // whitespace terminates
      | [] -> acc, [] // end of list terminates
      | c :: t -> token (acc + (c.ToString())) t // otherwise accumulate chars
   let rec tokenize' acc = function
      | w :: t when Char.IsWhiteSpace(w) -> tokenize' acc t // skip whitespace
      | '(' :: t -> tokenize' (Open :: acc) t
      | ')' :: t -> tokenize' (Close :: acc) t
      | '\'' :: t -> tokenize' (QuoteT :: acc) t
      | '`' :: t -> tokenize' (QuasiT :: acc) t
      | ',' :: t -> tokenize' (Unquote :: acc) t
      | ';' :: t -> comment t |> tokenize' acc // skip over comments
      | '"' :: t -> // start of string
         let s, t' = string "" t
         tokenize' (Token.String(s) :: acc) t'
      | '-' :: d :: t when Char.IsDigit(d) -> // start of negative number
         let n, t' = token ("-" + d.ToString()) t
         tokenize' (Token.Number(n) :: acc) t'
      | '+' :: d :: t | d :: t when Char.IsDigit(d) -> // start of positive number
         let n, t' = token (d.ToString()) t
         tokenize' (Token.Number(n) :: acc) t'
      | s :: t -> // otherwise start of symbol
         let s, t' = token (s.ToString()) t
         tokenize' (Token.Symbol(s) :: acc) t'
      | [] -> List.rev acc // end of list terminates
   tokenize' [] source

type Syntax =
   | Number_S of double
   | String_S of string
   | Symbol_S of string
   | Dot_S
   | Func_S of Func
   | List_S of Syntax list
   | Container_S of obj

type Macro = Syntax list -> Syntax
type MacroEnvironment = Map<string, Macro>

///Let* construct
let LetStar : Macro = function
   | List_S(bindings) :: body ->
     let folder b a = 
        match b with
        | List_S([Symbol_S(name); expr]) as bind ->
            List_S([Symbol_S("let"); List_S([bind]); a])
        | m -> failwith "bad let*"
     List.foldBack folder bindings <| List_S(Symbol_S("begin") :: body)
   | m -> failwith "bad let*"

///And Macro
let rec And : Macro = function
   | [] -> Symbol_S("#t")
   | [expr] -> expr
   | h :: t -> List_S([Symbol_S("if"); h; And t; Symbol_S("#f")])

///Or Macro
let rec Or : Macro = function
   | [] -> Symbol_S("#f")
   | [expr] -> expr
   | h :: t -> List_S([Symbol_S("if"); h; Symbol_S("#t"); Or t])

//Cond macro
let rec Cond : Macro = function
    | [List_S([Symbol_S("else"); expr])] -> expr
    | List_S([condition; expr]) :: t     -> List_S([Symbol_S("if"); condition; expr; Cond t])
    | []                                 -> List_S([Symbol_S("begin")])
    | m                                  -> failwith "bad cond"

let macroEnv = 
    Map.ofList [
       "let*", LetStar
       "cond", Cond
       "and", And
       "or", Or
    ]

///FScheme Macro delegate. Takes a list of unevaluated Values and an Environment as arguments, and returns a Value.
type ExternMacro = delegate of Syntax list -> Syntax

///Makes a Macro out of an ExternMacro
let makeExternMacro (ex : ExternMacro) : Macro = ex.Invoke

let rec printSyntax = function
    | Number_S(n)    -> n.ToString()
    | String_S(s)    -> "\"" + s + "\""
    | Symbol_S(s)    -> s
    | Func_S(_)      -> "#<procedure>"
    | Dot_S          -> "."
    | List_S(ps)     -> "(" + String.Join(" ", List.map printSyntax ps) + ")"
    | Container_S(o) -> sprintf "#<object:\"%s\">" <| o.ToString()

//A simple parser
let stringToSyntax source =
    let map = function
        | Token.Number(n)   -> Number_S(Double.Parse(n))
        | Token.String(s)   -> String_S(s)
        | Token.Symbol(".") -> Dot_S
        | Token.Symbol(s)   -> Symbol_S(s)
        | _                 -> failwith "Syntax error."
    let rec list f t acc =
        let e, t' = parse' [] t
        parse' (List_S(f e) :: acc) t'
    and parse' acc = function
        | Open :: t            -> list id t acc
        | Close :: t           -> (List.rev acc), t
        | QuoteT :: Open :: t  -> list (fun e -> [Symbol_S("quote"); List_S(e)]) t acc
        | QuoteT :: h :: t     -> parse' (List_S([Symbol_S("quote"); map h]) :: acc) t
        | QuasiT :: Open :: t  -> list (fun e -> [Symbol_S("quasiquote"); List_S(e)]) t acc
        | QuasiT :: h :: t     -> parse' (List_S([Symbol_S("quasiquote"); map h]) :: acc) t
        | Unquote :: Open :: t -> list (fun e -> [Symbol_S("unquote"); List_S(e)]) t acc
        | Unquote :: h :: t    -> parse' (List_S([Symbol_S("unquote"); map h]) :: acc) t
        | h :: t               -> parse' ((map h) :: acc) t
        | []                   -> (List.rev acc), []
    let result, _ = parse' [] (tokenize source)
    result

type Parameter =
    | Normal of string
    | Tail of string

///AST for FScheme expressions
type Expression =
    | Number_E of double
    | String_E of string
    | Id of string
    | SetId of string * Expression
    | Let of string list * Expression list * Expression
    | LetRec of string list * Expression list * Expression
    | Fun of Parameter list * Expression
    | List_E of Expression list
    | If of Expression * Expression * Expression
    | Define of string * Expression
    | Begin of Expression list
    | Quote of Syntax
    | Quasi of Syntax
    | Function_E of Func
    | Container_E of obj
    | Value_E of Value

let rec printExpression indent syntax =
    let printLet name names exprs body =
        "(" + name +  " ("
            + String.Join(
                "\n" + indent + "      ",
                List.map (function (n, b) -> "[" + n + (printExpression " " b) + "]")
                         (List.zip names exprs))
            + ")\n"
            + printExpression (indent + "  ") body
            + ")"
    let printParam = function Normal(s) | Tail(s) -> s
    indent + match syntax with
             | Number_E(n)                -> n.ToString()
             | String_E(s)                -> "\"" + s + "\""
             | Id(s)                      -> s
             | SetId(s, expr)             -> "(set! " + s + " " + printExpression "" expr + ")"
             | Let(names, exprs, body)    -> printLet "let" names exprs body
             | LetRec(names, exprs, body) -> printLet "letrec" names exprs body
             | Fun(names, body)           -> "(λ (" + String.Join(" ", List.map printParam names) + ") " + printExpression "" body + ")"
             | List_E(exprs)              -> "(" + String.Join(" ", List.map (printExpression "") exprs) + ")"
             | If(c, t, e)                -> "(if " + String.Join(" ", List.map (printExpression "") [c; t; e]) + ")"
             | Define(name, body)         -> "(define " + name + printExpression " " body + ")"
             | Begin(exprs)               -> "(begin " + String.Join(" ", List.map (printExpression "") exprs) + ")"
             | Quote(p)                   -> "(quote " + printSyntax p + ")"
             | Quasi(p)                   -> "(quasiquote " + printSyntax p + ")"
             | Function_E(_)              -> "#<procedure>"
             | Container_E(o)             -> sprintf "#<object:\"%s\">" <| o.ToString()
             | Value_E(v)                 -> print v

//A simple parser
let rec syntaxToExpression (macro_env : MacroEnvironment) parser =
    let parse' = syntaxToExpression macro_env
    match parser with
    | Dot_S          -> failwith "illegal use of \".\""
    | Number_S(n)    -> Number_E(n)
    | String_S(s)    -> String_E(s)
    | Symbol_S(s)    -> Id(s)
    | Func_S(f)      -> Function_E(f)
    | Container_S(o) -> Container_E(o)
    | List_S([])     -> List_E([])
    | List_S(h :: t) ->
        match h with
        //Set!
        | Symbol_S("set!") ->
            match t with
            | Symbol_S(name) :: body -> SetId(name, Begin(List.map parse' body))
            | m                      -> failwith "Syntax error in set!"

        //let and letrec
        | Symbol_S(s) when s = "let" || s = "letrec" ->
            match t with
            | List_S(bindings) :: body ->
                let rec makeLet names bndings = function
                    | List_S([Symbol_S(name); bind]) :: t ->
                        makeLet (name :: names) ((parse' bind) :: bndings) t
                    | [] ->
                        let f = if s = "let" then Let else LetRec
                        f(names, bndings, Begin(List.map parse' body))
                    | m -> failwith <| sprintf "Syntax error in %s bindings." s
                makeLet [] [] bindings
            | m -> failwith <| sprintf "Syntax error in %s." s

        //lambda
        | Symbol_S("lambda") | Symbol_S("λ") ->
            match t with
            | List_S(parameters) :: body ->
                let rec paramMap acc = function
                    | [Dot_S; Symbol_S(s)] -> Tail(s) :: acc |> List.rev
                    | Symbol_S(s) :: t     -> paramMap (Normal(s) :: acc) t
                    | []                   -> List.rev acc
                    | m                    -> failwith "Syntax error in function definition."
                Fun(paramMap [] parameters, Begin(List.map parse' body))
            | m -> List_S(t) |> printSyntax |> sprintf "Syntax error in function definition: %s" |> failwith

        //if
        | Symbol_S("if") ->
            match t with
            | [cond; then_case]            -> If(parse' cond, parse' then_case, Begin([]))
            | [cond; then_case; else_case] -> If(parse' cond, parse' then_case, parse' else_case)
            | m                            -> failwith "Syntax error in if"//: %s" expr |> failwith

        //define
        | Symbol_S("define") as d ->
            match t with
            | Symbol_S(name) :: body -> Define(name, Begin(List.map parse' body))
            | List_S(name :: ps) :: body ->
                parse' <| List_S([d; name; List_S(Symbol_S("lambda") :: List_S(ps) :: body)])
            | m -> failwith "Syntax error in define"//: %s" expr |> failwith

        //quote
        | Symbol_S("quote") ->
            match t with
            | [expr] -> Quote(expr)
            | m      -> failwith "Syntax error in quote"
        | Symbol_S("quasiquote") ->
            match t with
            | [expr] -> Quasi(expr)
            | m      -> failwith "Syntax error in quasiquote"

        //unquote
        | Symbol_S("unquote") -> failwith "unquote outside of quote"

        //begin
        | Symbol_S("begin") -> Begin(List.map parse' t)

        //defined macros
        | Symbol_S(s) when macro_env.ContainsKey s ->  parse' <| macro_env.[s] t

        //otherwise...
        | _ -> List_E(List.map parse' <| h :: t)

let parse = stringToSyntax >> List.map (syntaxToExpression macroEnv)