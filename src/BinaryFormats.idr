module BinaryFormats

import Control.Pipeline
import Data.Vect

%default total

||| A binary digit (either 0 or 1)
data Bit : Type where
    ||| The 0 digit
    O : Bit
    ||| The 1 digit
    I : Bit

mutual
    ||| A universe of binary data formats
    data Format : Type where
        FBad : Format
        FEnd : Format
        FBit : Format
        FChar : Format
        FNat : Format
        FVect : Nat -> Format -> Format
        FPlus : Format -> Format -> Format
        FSkip : Format -> Format -> Format
        FRead : (f : Format) -> (embed f -> Format) -> Format

    ||| Interprets `Format` as an Idris type
    embed : Format -> Type
    embed FBad = Void
    embed FEnd = Unit
    embed FBit = Bit
    embed FChar = Char
    embed FNat = Nat
    embed (FVect n a) = Vect n (embed a)
    embed (FPlus f1 f2) = Either (embed f1) (embed f2)
    embed (FSkip _ f) = embed f
    embed (FRead f1 f2) = (f : embed f1 ** embed (f2 f))

||| Require a predicate to be satisfied
satisfy : (f : Format) -> (embed f -> Bool) -> Format
satisfy f pred =
    FRead f  (\x => if pred x then FEnd else FBad)

||| Require a character literal to be parsed
char : Char -> Format
char c =
    satisfy FChar ((==) c)

||| Sequence two binary formats, one after the other
(>>) : Format -> Format -> Format
(>>) x f = FSkip x f

||| Parsed one format and then use it to figure out what to parse next
(>>=) : (f : Format) -> (embed f -> Format) -> Format
(>>=) x f = FRead x f

Parser : Type -> Type
Parser a = (bits : List Bit) -> Maybe (a, List Bit)

parseChar : Parser Char
parseChar bits =
    ?parseChar_rhs

parseNat : Parser Nat
parseNat bits =
    ?parseNat_rhs

mutual
    -- TODO: make this tail-recursive?
    parseVect : {n : Nat} -> %static (f : Format) -> Parser (Vect n (embed f))
    parseVect {n = Z} _ bits = Just ([], bits)
    parseVect {n = (S k)} f bits with (parse f bits)
        | Nothing = Nothing
        | Just (x, bits') =
            parseVect {n = k} f bits'
                |> map (\(xs, bits'') => (x :: xs, bits''))

    ||| Interpret a binary format specification as a parser
    parse : %static (f : Format) -> Parser (embed f)
    parse FBad bits = Nothing
    parse FEnd bits = Just ((), bits)
    parse FBit (bit :: bits) = Just (bit, bits)
    parse FChar bits = parseChar bits
    parse FNat bits = parseNat bits
    parse (FVect n f) bits = parseVect f bits
    parse (FPlus f1 f2) bits with (parse f1 bits)
        | (Just (x, bits')) = Just (Left x, bits')
        | Nothing with (parse f2 bits)
            | (Just (y, bits')) = Just (Right y, bits')
            | Nothing = Nothing
    parse (FSkip f1 f2) bits with (parse f1 bits)
        | Nothing = Nothing
        | (Just (x, bits')) = parse f2 bits'
    parse (FRead f1 f2) bits with (parse f1 bits)
        | Nothing = Nothing
        | (Just (x, bits')) with (parse (f2 x) bits')
            | Nothing = Nothing
            | Just (y, bits'') = Just ((x ** y), bits'')

||| PBM binary format
pbm : Format
pbm = do
    char 'p'
    char '4'
    char ' '
    n <- FNat
    char ' '
    m <- FNat
    char '\n'
    bs <- FVect n (FVect m FBit)
    FEnd

||| Parse PBM data from a string of bits
parsePbm : Parser (embed BinaryFormats.pbm)
parsePbm = parse pbm