open System
open System.IO

let memory = Array.create 0x10000 0us

let mutable buf = 0
let input () =
    let buffer = 0x9000
    let size = 16
    if Console.KeyAvailable then
        let b = buffer + buf
        memory.[b] <- uint16 (Console.ReadKey true).KeyChar
        if memory.[b] = 13us then memory.[b] <- 10us // CR –> LF
        memory.[buffer + size] <- uint16 (b)
        buf <- (buf + 1) % size

let vidwidth, vidheight = 32, 12
Console.Clear()
Console.WindowWidth <- vidwidth
Console.WindowHeight <- vidheight
Console.CursorVisible <- false
Console.Title <- "F# DCPU-16"

let output i =
    let vidmem = 0x8000
    if i >= vidmem && i <= vidmem + vidwidth * vidheight then
        let p = i - vidmem
        Console.SetCursorPosition(p % vidwidth, p / vidwidth)
        let v = int memory.[i]
        Console.BackgroundColor <- (v >>> 8) &&& 0x0f |> enum
        Console.ForegroundColor <- v >>> 12 |> enum
        Console.Write(v &&& 0x7f |> char)

let registers = Array.create 11 0us

let rec cycle () =
    input ()
    let mem i = (fun () -> memory.[i] |> int), (fun v -> memory.[i] <- uint16 v; output i)
    let reg i = (fun () -> registers.[i] |> int), (fun v -> registers.[i] <- uint16 v)
    let lit v = (fun () -> v), (fun _ -> ())
    let pc, sp, o = reg 8, reg 9, reg 10
    let get v = (fst v) ()
    let set v i = (snd v) i
    let next () = let p = get pc in let n = mem p |> get in set pc (p + 1); n
    let decode () = let i = next () in i, (i &&& 0x3f0) >>> 4 |> int, (i &&& 0xfc00) >>> 10 |> int
    let skip () =
        let skip' i = if (i > 0xf && i < 0x18) || i = 0x1e || i = 0x1f then get pc + 1 |> set pc else ()
        let _, a, b = decode ()
        skip' a; skip' b
    let value = function
        | x when x <= 0x07 -> reg x // reg
        | x when x <= 0x0f -> (x &&& 0b111 |> reg |> fst) () |> mem // [reg]
        | x when x <= 0x17 -> (x &&& 0b111 |> reg |> fst) () + next () |> mem // [next + reg]
        | 0x18 -> let s = get sp in let x = mem s in set sp (s + 1); x // POP / [SP++]
        | 0x19 -> get sp |> mem // PEEK / [SP]
        | 0x1a -> get sp - 1 |> set sp; get sp |> mem // PUSH / [--SP]
        | 0x1b -> sp // SP
        | 0x1c -> pc // PC
        | 0x1d -> o // O
        | 0x1e -> next () |> mem // [next]
        | 0x1f -> next () |> lit // next (literal)
        | x -> x - 0x20 |> lit // literal 0x00-0x1f
    let instruction, a', b' = decode ()
    let a, b = value a', value b'
    let fxy f = f (get a) (get b)
    let fop op = fxy (fun x y -> op x y |> set a)
    let fif op = fxy (fun x y -> if op x y then skip ())
    match instruction &&& 0xf |> int with
    | 0x0 -> if a' = 0x01 then get pc |> set (value 0x1a (* PUSH *)); get b |> set pc // JSR
    | 0x1 -> get b |> set a // SET
    | 0x2 -> fxy (fun x y -> x + y |> set a; set o (if x + y > 0xffff then 1 else 0)) // ADD
    | 0x3 -> fxy (fun x y -> x - y |> set a; set o (if x - y < 0 then 0xffff else 0)) // SUB
    | 0x4 -> fxy (fun x y -> x * y |> set a; ((x * y) >>> 16) |> set o) // MUL
    | 0x5 -> fxy (fun x y -> if y = 0 then set a 0; set o 0 else x / y |> set a; (x <<< 16) / y |> set o) // DIV
    | 0x6 -> fxy (fun x y -> set a (if y = 0 then 0 else x % y)) // MOD
    | 0x7 -> fxy (fun x y -> let z = x <<< y in set a z; z >>> 16 |> set o) // SHL
    | 0x8 -> fxy (fun x y -> x >>> y |> set a; (x <<< 16) >>> y |> set o) // SHR
    | 0x9 -> fop (&&&) // AND
    | 0xa -> fop (|||) // BOR
    | 0xb -> fop (^^^) // XOR
    | 0xc -> fif (<>) // IFE
    | 0xd -> fif (=) // IFN
    | 0xe -> fif (<=) // IFG
    | 0xf -> fif (fun x y -> x &&& y = 0) // IFB
    cycle ()

// Load Matt Hellige's GoForth!
// Image file from http://matt.immute.net/files/goforth/goforth.img
// See also https://github.com/hellige/dcpu)
let image = File.ReadAllBytes @"..\..\goforth.img"
for i in 0 .. 2 .. image.Length - 1 do
    memory.[i / 2] <- (uint16 image.[i]) <<< 8 ||| uint16 image.[i + 1]

cycle ()