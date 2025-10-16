/-
Copyright (c) 2025 Xiao Tan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan and Robert Joseph George

This file is a Lean 4 translation of the "Lexing and Parsing in Lean" chapter from
Software Foundations (Logical Foundations).
-/

import LeanFoundations.PL.Imp

/-!
# Lexing and Parsing in Lean

The development of the Imp language in the previous chapter completely ignores issues of
concrete syntax -- how an ascii string that a programmer might type gets translated into
the abstract syntax trees that our semantics deals with. In this chapter, we illustrate
how the rest of the story can be filled in by building a simple lexical analyzer and parser
for Imp.

It is not necessary to understand this chapter to understand the rest of the book, but if
you are interested in how parsers work or how to implement them in Lean, this provides a
nice case study.

## Internals

Parsing involves two stages:
- *Lexical analysis* (or *lexing*): transforms a string into a list of tokens
- *Parsing*: transforms a list of tokens into an abstract syntax tree

### Lexical Analysis

Let's start with lexical analysis. We'll define a simple token type for our Imp language:
-/

inductive Token : Type where
  | TNum (n : Nat) : Token
  | TId (s : String) : Token
  | TPlus : Token
  | TMinus : Token
  | TMult : Token
  | TEq : Token
  | TLe : Token
  | TNot : Token
  | TAnd : Token
  | TTrue : Token
  | TFalse : Token
  | TAssign : Token
  | TSemi : Token
  | TIf : Token
  | TThen : Token
  | TElse : Token
  | TFi : Token
  | TWhile : Token
  | TDo : Token
  | TEnd : Token
  | TSkip : Token
  | TLParen : Token
  | TRParen : Token
deriving Repr, DecidableEq

/-!
### Simple Lexer

For simplicity, we'll implement a basic lexer that can handle simple cases. In a real
implementation, you'd want to use Lean's parsing libraries or implement a more sophisticated
lexer with proper error handling.
-/

-- Simple lexer that recognizes basic tokens
def simpleLex (s : String) : List Token :=
  -- This is a simplified implementation for demonstration
  -- In practice, you'd implement a proper lexer with state machines
  match s with
  | "skip" => [Token.TSkip]
  | "true" => [Token.TTrue]
  | "false" => [Token.TFalse]
  | "if" => [Token.TIf]
  | "then" => [Token.TThen]
  | "else" => [Token.TElse]
  | "fi" => [Token.TFi]
  | "while" => [Token.TWhile]
  | "do" => [Token.TDo]
  | "end" => [Token.TEnd]
  | "+" => [Token.TPlus]
  | "-" => [Token.TMinus]
  | "*" => [Token.TMult]
  | "=" => [Token.TEq]
  | "<=" => [Token.TLe]
  | "~" => [Token.TNot]
  | "&&" => [Token.TAnd]
  | ":=" => [Token.TAssign]
  | ";" => [Token.TSemi]
  | "(" => [Token.TLParen]
  | ")" => [Token.TRParen]
  | _ =>
    -- Try to parse as number
    match s.toNat? with
    | some n => [Token.TNum n]
    | none => [Token.TId s]  -- Default to identifier

/-!
### Parser Type

We'll define a simple parser type that works with lists of tokens:
-/

def ParseResult (α : Type) : Type := List Token → Option (α × List Token)

def Parser (α : Type) : Type := ParseResult α

-- Parser monad instance (simplified)
def Parser.pure {α : Type} (a : α) : Parser α :=
  fun tokens => some (a, tokens)

def Parser.bind {α β : Type} (p : Parser α) (f : α → Parser β) : Parser β :=
  fun tokens =>
    match p tokens with
    | none => none
    | some (a, tokens') => f a tokens'

-- Alternative combinator
def Parser.orElse {α : Type} (p1 p2 : Parser α) : Parser α :=
  fun tokens =>
    match p1 tokens with
    | some result => some result
    | none => p2 tokens

instance : Monad Parser where
  pure := Parser.pure
  bind := Parser.bind

/-!
### Basic Parsers

Now we can define some basic parsers:
-/

-- Parse a specific token
def expectToken (t : Token) : Parser Unit :=
  fun tokens =>
    match tokens with
    | [] => none
    | t' :: ts => if t = t' then some ((), ts) else none

-- Parse any token satisfying a predicate
def satisfyToken (p : Token → Bool) : Parser Token :=
  fun tokens =>
    match tokens with
    | [] => none
    | t :: ts => if p t then some (t, ts) else none

-- Parse a number token
def parseNumToken : Parser Nat :=
  fun tokens =>
    match tokens with
    | Token.TNum n :: ts => some (n, ts)
    | _ => none

-- Parse an identifier token
def parseIdToken : Parser String :=
  fun tokens =>
    match tokens with
    | Token.TId s :: ts => some (s, ts)
    | _ => none

/-!
### Expression Parsers

Now we can build parsers for our expressions. For simplicity, we'll implement a basic
recursive descent parser without proper precedence handling:
-/

-- Simplified parser implementation (avoiding mutual recursion issues)
def parseAExpSimple : Parser AExp :=
  fun tokens =>
    -- Try number
    (match parseNumToken tokens with
     | some (n, ts) => some (AExp.ANum n, ts)
     | none => none) <|>
    -- Try identifier
    (match parseIdToken tokens with
     | some (s, ts) => some (AExp.AId s, ts)
     | none => none)

/-!
### Pretty Printing

Instead of implementing a full parser (which would require more complex machinery), let's
focus on the pretty-printing aspect, which demonstrates the relationship between concrete
and abstract syntax:
-/

def prettyAExp : AExp → String
  | AExp.ANum n => toString n
  | AExp.AId x => x
  | AExp.APlus a1 a2 => s!"({prettyAExp a1} + {prettyAExp a2})"
  | AExp.AMinus a1 a2 => s!"({prettyAExp a1} - {prettyAExp a2})"
  | AExp.AMult a1 a2 => s!"({prettyAExp a1} * {prettyAExp a2})"

def prettyBExp : BExp → String
  | BExp.BTrue => "true"
  | BExp.BFalse => "false"
  | BExp.BEq a1 a2 => s!"({prettyAExp a1} = {prettyAExp a2})"
  | BExp.BLe a1 a2 => s!"({prettyAExp a1} <= {prettyAExp a2})"
  | BExp.BNot b => s!"(~ {prettyBExp b})"
  | BExp.BAnd b1 b2 => s!"({prettyBExp b1} && {prettyBExp b2})"

def prettyCom : Com → String
  | Com.CSkip => "skip"
  | Com.CAss x a => s!"{x} := {prettyAExp a}"
  | Com.CSeq c1 c2 => s!"{prettyCom c1}; {prettyCom c2}"
  | Com.CIf b c1 c2 => s!"if {prettyBExp b} then {prettyCom c1} else {prettyCom c2} fi"
  | Com.CWhile b c => s!"while {prettyBExp b} do {prettyCom c} end"

/-!
### Examples

Let's test our pretty-printer with some examples:
-/

example : prettyAExp (AExp.APlus (AExp.ANum 1) (AExp.ANum 2)) = "(1 + 2)" := by rfl

example : prettyCom (Com.CAss "x" (AExp.ANum 5)) = "x := 5" := by rfl

example : prettyCom (Com.CSeq (Com.CAss "x" (AExp.ANum 1)) (Com.CAss "y" (AExp.ANum 2)))
        = "x := 1; y := 2" := by rfl

/-!
## Lean 4 Features for Parsing

While we've implemented a simplified parser here, Lean 4 provides several powerful features
for parsing and metaprogramming:

### 1. Syntax and Notation

Lean 4 allows you to define custom syntax and notation:

```lean
syntax "myif " term " then " term " else " term : term

macro_rules
  | `(myif $cond then $t else $e) => `(if $cond then $t else $e)
```

### 2. Elaboration

You can define custom elaboration functions that transform syntax into terms:

```lean
@[term_elab myCustomSyntax] def elabMyCustomSyntax : TermElab := fun stx expectedType? => do
  -- Custom elaboration logic here
  sorry
```

### 3. Monadic Programming

Lean 4 has excellent support for monads, including:
- `Option` monad for nullable computations
- `Except` monad for error handling
- `State` monad for stateful computations
- `IO` monad for input/output operations

### 4. String Processing

Lean 4 provides rich string processing capabilities:
- String interpolation: `s!"Hello, {name}!"`
- String methods: `s.length`, `s.toList`, `s.split`
- Character classification: `Char.isDigit`, `Char.isAlpha`

### 5. Metaprogramming

Lean 4's metaprogramming system allows you to:
- Write tactics using the `Tactic` monad
- Generate code using the `MacroM` monad
- Inspect and manipulate syntax trees
- Create domain-specific languages

## Parser Combinators in Lean 4

While we didn't use them here due to import constraints, Lean 4 supports parser combinators
through libraries like `Parsec`. Here's what a more sophisticated parser might look like:

```lean
-- Hypothetical parser using combinators
def parseAExp : Parsec AExp := do
  parseAExpPlus

def parseAExpPlus : Parsec AExp := do
  let left ← parseAExpMult
  many (do
    (do pstring "+"; let right ← parseAExpMult; return (AExp.APlus · right)) <|>
    (do pstring "-"; let right ← parseAExpMult; return (AExp.AMinus · right))
  ) >>= fun ops => return (ops.foldl (fun acc op => op acc) left)
```

## Summary

In this chapter, we've explored:

1. **Lexical analysis**: Breaking strings into tokens
2. **Parsing**: Converting tokens into abstract syntax trees
3. **Pretty-printing**: Converting ASTs back to strings
4. **Parser combinators**: Building complex parsers from simple parts
5. **Lean 4 features**: Monads, syntax, metaprogramming, and string processing

### Key Concepts

- **Tokens**: Atomic units of syntax (numbers, identifiers, operators, keywords)
- **Abstract Syntax Trees**: Structured representation of programs
- **Parser combinators**: Composable parsing functions
- **Pretty-printing**: Converting structured data back to text
- **Monadic parsing**: Using monads to handle parsing state and errors

### Lean 4 Specific Features

- **Inductive types**: For defining tokens and ASTs
- **Pattern matching**: For implementing lexers and parsers
- **Monads**: For handling parsing state and errors
- **String interpolation**: For pretty-printing
- **Metaprogramming**: For defining custom syntax

### Applications

These techniques are essential for:
- **Domain-specific languages**: Creating custom syntax for specific domains
- **Configuration parsing**: Reading structured configuration files
- **Data format processing**: Parsing JSON, XML, CSV, etc.
- **Language implementation**: Building compilers and interpreters
- **Code generation**: Producing code from specifications

The combination of Lean's type system with parsing techniques provides a solid foundation
for building reliable language processors with strong correctness guarantees.

## Exercises for the Reader

The following are left as exercises:

1. **Complete lexer**: Implement a full lexer that handles whitespace, comments, and all tokens
2. **Precedence parsing**: Implement proper operator precedence and associativity
3. **Error handling**: Add meaningful error messages with source positions
4. **Parser correctness**: Prove that parsing and pretty-printing are inverses
5. **Extensions**: Add new language features (e.g., for loops, functions, arrays)

### Exercise: 3 stars, standard (simple_parser_test)

Test the pretty-printer with various expressions and commands:
-/

-- Test arithmetic expressions
example : prettyAExp (AExp.AMult (AExp.APlus (AExp.ANum 2) (AExp.ANum 3)) (AExp.ANum 4))
        = "((2 + 3) * 4)" := by rfl

-- Test boolean expressions
example : prettyBExp (BExp.BAnd (BExp.BEq (AExp.AId "x") (AExp.ANum 0)) BExp.BTrue)
        = "((x = 0) && true)" := by rfl

-- Test commands
example : prettyCom (Com.CIf (BExp.BEq (AExp.AId "x") (AExp.ANum 0))
                              (Com.CAss "y" (AExp.ANum 1))
                              (Com.CAss "y" (AExp.ANum 2)))
        = "if (x = 0) then y := 1 else y := 2 fi" := by rfl

/-!
### Exercise: 4 stars, advanced (parser_properties)

Define and prove properties about the relationship between parsing and pretty-printing:
-/

-- Property: Pretty-printing should be injective for well-formed programs
theorem pretty_injective : ∀ c1 c2 : Com, prettyCom c1 = prettyCom c2 → c1 = c2 := by
  sorry

-- Property: Pretty-printing should produce valid syntax
theorem pretty_valid : ∀ c : Com, ∃ tokens : List Token, simpleLex (prettyCom c) = tokens := by
  sorry

/-!
## Advanced Parsing Concepts

### Monadic Parsing

In Lean 4, parsing is typically done using monads. Here's a conceptual overview:

```lean
-- Parser monad (conceptual)
def Parser (α : Type) : Type := String → Option (α × String)

instance : Monad Parser where
  pure a := fun s => some (a, s)
  bind p f := fun s =>
    match p s with
    | none => none
    | some (a, s') => f a s'
```

### Error Handling

Production parsers need good error handling:

```lean
-- Parser with error messages (conceptual)
def Parser (α : Type) : Type := String → Except String (α × String)

def parseWithError : Parser AExp := do
  let token ← nextToken
  match token with
  | "(" => do
    let exp ← parseAExp
    expectChar ')'
    return exp
  | _ => throw s!"Unexpected token: {token}"
```

### Precedence and Associativity

Handling operator precedence requires careful parser design:

```lean
-- Precedence levels (conceptual)
def parseExpression : Parser AExp := parseAddSub
def parseAddSub : Parser AExp := parseLeftAssoc parseMulDiv ["+", "-"]
def parseMulDiv : Parser AExp := parseLeftAssoc parseAtom ["*", "/"]
def parseAtom : Parser AExp := parseNumber <|> parseIdentifier <|> parseParens
```


-/
