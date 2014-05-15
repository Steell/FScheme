module FScheme.Parser

open FScheme.Value

open System

//Simple Tokenizer for quickly defining Values in Scheme syntax.
type Token =
   | Open | Close
   | Quote | Quasi | Unquote
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
      | '\'' :: t -> tokenize' (Quote :: acc) t
      | '`' :: t -> tokenize' (Quasi :: acc) t
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

type Parser =
   | Number_P of double
   | String_P of string
   | Symbol_P of string
   | Func_P of Func
   | List_P of Parser list

type Macro = Parser list -> Parser
type MacroEnvironment = Map<string, Macro>

///Let* construct
let LetStar : Macro = function
   | List_P(bindings) :: body ->
     let folder b a = 
        match b with
        | List_P([Symbol_P(name); expr]) as bind ->
            List_P([Symbol_P("let"); List_P([bind]); a])
        | m -> failwith "bad let*"
     List_P(Symbol_P("begin") :: body) |> List.foldBack folder bindings 
   | m -> failwith "bad let*"

///And Macro
let rec And : Macro = function
   | [] -> Number_P(1.0)
   | [expr] -> expr
   | h :: t -> List_P([Symbol_P("if"); h; And t; Number_P(0.0)])

///Or Macro
let rec Or : Macro = function
   | [] -> Number_P(0.0)
   | [expr] -> expr
   | h :: t -> List_P([Symbol_P("if"); h; Number_P(1.0); Or t])

let macroEnv = 
    Map.ofList [
       "let*", LetStar
       "and", And
       "or", Or
    ]

///FScheme Macro delegate. Takes a list of unevaluated Values and an Environment as arguments, and returns a Value.
type ExternMacro = delegate of Parser list -> Parser

///Makes a Macro out of an ExternMacro
let makeExternMacro (ex : ExternMacro) : Macro = ex.Invoke

let rec printParser = function
   | Number_P(n) -> n.ToString()
   | String_P(s) -> "\"" + s + "\""
   | Symbol_P(s) -> s
   | Func_P(_) -> "#<procedure>"
   | List_P(ps) -> "(" + String.Join(" ", List.map printParser ps) + ")"

//A simple parser
let stringToParser source =
   let map = function
      | Token.Number(n) -> Number_P(Double.Parse(n))
      | Token.String(s) -> String_P(s)
      | Token.Symbol(s) -> Symbol_P(s)
      | _ -> failwith "Syntax error."
   let rec list f t acc =
      let e, t' = parse' [] t
      parse' (List_P(f e) :: acc) t'
   and parse' acc = function
      | Open :: t -> list id t acc
      | Close :: t -> (List.rev acc), t
      | Quote :: Open :: t -> list (fun e -> [Symbol_P("quote"); List_P(e)]) t acc
      | Quote :: h :: t -> parse' (List_P([Symbol_P("quote"); map h]) :: acc) t
      | Quasi :: Open :: t -> list (fun e -> [Symbol_P("quasiquote"); List_P(e)]) t acc
      | Quasi :: h :: t -> parse' (List_P([Symbol_P("quasiquote"); map h]) :: acc) t
      | Unquote :: Open :: t -> list (fun e -> [Symbol_P("unquote"); List_P(e)]) t acc
      | Unquote :: h :: t -> parse' (List_P([Symbol_P("unquote"); map h]) :: acc) t
      | h :: t -> parse' ((map h) :: acc) t
      | [] -> (List.rev acc), []
   let result, _ = parse' [] (tokenize source)
   result

///AST for FScheme Values
type Syntax =
   | Number_S of double
   | String_S of string
   | Id of string
   | SetId of string * Syntax
   | Bind of string list * Syntax list * Syntax
   | BindRec of string list * Syntax list * Syntax
   | Fun of string list * Syntax
   | List_S of Syntax list
   | If of Syntax * Syntax * Syntax
   | Define of string * Syntax
   | Begin of Syntax list
   | Quote_S of Parser
   | Quasi_S of Parser
   | Func_S of Func

let rec printSyntax indent syntax = 
   let printBind name names exprs body =
      "(" + name +  " (" 
         + String.Join(
            "\n" + indent + "      ", 
            (List.map (function (n, b) -> "[" + n + (printSyntax " " b) + "]")
                      (List.zip names exprs)))
         + ")\n"
         + (printSyntax (indent + "  ") body)
         + ")"
   indent + match syntax with
            | Number_S(n) -> n.ToString()
            | String_S(s) -> "\"" + s + "\""
            | Id(s) -> s
            | SetId(s, expr) -> "(set! " + s + " " + printSyntax "" expr
            | Bind(names, exprs, body) -> printBind "let" names exprs body
            | BindRec(names, exprs, body) -> printBind "letrec" names exprs body
            | Fun(names, body) -> "(lambda (" + String.Join(" ", names) + ") " + printSyntax "" body + ")"
            | List_S(exprs) -> "(" + String.Join(" ", (List.map (printSyntax "") exprs)) + ")"
            | If(c, t, e) -> "(if " + String.Join(" ", (List.map (printSyntax "") [c; t; e])) + ")"
            | Define(names, body) -> "(define (" + String.Join(" ", names) + ")" + printSyntax " " body + ")"
            | Begin(exprs) -> "(begin " + String.Join(" ", (List.map (printSyntax "") exprs)) + ")"
            | Quote_S(p) -> "(quote " + printParser p + ")"
            | Quasi_S(p) -> "(quasiquote " + printParser p + ")"
            | Func_S(_) -> "#<procedure>"

//A simple parser
let rec parserToSyntax (macro_env : MacroEnvironment) parser =
    let parse' = parserToSyntax macro_env
    match parser with
    | Number_P(n) -> Number_S(n)
    | String_P(s) -> String_S(s)
    | Symbol_P(s) -> Id(s)
    | List_P([]) -> List_S([])
    | Func_P(f) -> Func_S(f)
    | List_P(h :: t) ->
        match h with
        //Set!
        | Symbol_P("set!") ->
            match t with
            | Symbol_P(name) :: body -> SetId(name, Begin(List.map parse' body))
            | m -> failwith "Syntax error in set!"
        //let and letrec
        | Symbol_P(s) when s = "let" || s = "letrec" ->
            match t with
            | List_P(bindings) :: body ->
               let rec makeBind names bndings = function
                  | List_P([Symbol_P(name); bind]) :: t -> makeBind (name :: names) ((parse' bind) :: bndings) t
                  | [] -> 
                    let f = if s = "let" then Bind else BindRec
                    f(names, bndings, Begin(List.map parse' body))
                  | m -> sprintf "Syntax error in %s bindings." s |> failwith
               makeBind [] [] bindings
            | m -> sprintf "Syntax error in %s." s |> failwith
        //lambda
        | Symbol_P("lambda") | Symbol_P("λ") ->
            match t with
            | List_P(parameters) :: body ->
               Fun(List.map (function Symbol_P(s) -> s | m -> failwith "Syntax error in function definition.") parameters, Begin(List.map parse' body))
            | m -> List_P(t) |> printParser |> sprintf "Syntax error in function definition: %s" |> failwith
        //if
        | Symbol_P("if") ->
            match t with
            | [cond; then_case; else_case] -> If(parse' cond, parse' then_case, parse' else_case)
            | m -> failwith "Syntax error in if"//: %s" expr |> failwith
        //define
        | Symbol_P("define") -> 
            match t with
            | List_P(Symbol_P(name) :: parameters) :: body ->
                let ps = List.map (function Symbol_P(name) -> name | m -> failwith "Syntax error in define") parameters
                Define(name, Fun(ps, Begin(List.map parse' body)))
            | Symbol_P(name) :: body -> Define(name, Begin(List.map parse' body))
            | m -> failwith "Syntax error in define"//: %s" expr |> failwith
        //quote
        | Symbol_P("quote") ->
            match t with
            | [expr] -> Quote_S(expr)
            | m -> failwith "Syntax error in quote"
        | Symbol_P("quasiquote") -> 
            match t with
            | [expr] -> Quasi_S(expr)
            | m -> failwith "Syntax error in quasiquote"
        //unquote
        | Symbol_P("unquote") ->
            failwith "unquote outside of quote"
        //begin
        | Symbol_P("begin") ->
            Begin(List.map parse' t)
        //defined macros
        | Symbol_P(s) when macro_env.ContainsKey s ->
            macro_env.[s] t |> parse'
        //otherwise...
        | _ -> List_S(List.map parse' (h :: t))

let parse = stringToParser >> List.map (parserToSyntax macroEnv)