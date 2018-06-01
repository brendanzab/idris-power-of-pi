module BinaryFormats

import Control.Pipeline
import Data.Vect
import Data.ZZ

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
        FU8 : Format -- TODO: Endianness
        FU16 : Format -- TODO: Endianness
        FU32 : Format -- TODO: Endianness
        FS8 : Format -- TODO: Endianness
        FS16 : Format -- TODO: Endianness
        FS32 : Format -- TODO: Endianness
        FOffset : Nat -> Format -> Format
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
    embed FU8 = Nat
    embed FU16 = Nat
    embed FU32 = Nat
    embed FS8 = ZZ
    embed FS16 = ZZ
    embed FS32 = ZZ
    embed (FOffset _ f) = Lazy (Maybe (embed f))
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

parseBit : Parser Bit
parseBit [] = Nothing
parseBit (bit :: bits) = Just (bit, bits)

trySplitAt : {a : Type} -> Nat -> List a -> Maybe (List a, List a)
trySplitAt offset bits =
    toMaybe (length bits < offset) (splitAt offset bits)

tryDrop : {a : Type} -> Nat -> List a -> Maybe (List a)
tryDrop offset bits =
    toMaybe (length bits < offset) (drop offset bits)

parseUInt : Nat -> Parser Nat
parseUInt size bits =
    trySplitAt size bits
        |> map (\(headBits, tailBits) => (go headBits 0, tailBits))
    where
        go : List Bit -> Nat -> Nat
        go [] acc = acc
        go (O :: bits) acc = go bits (2 * acc)
        go (I :: bits) acc = go bits (S (2 * acc))

parseSInt : Nat -> Parser ZZ
parseSInt Z bits = Just (0, bits)
parseSInt (S _) [] = Nothing
parseSInt (S size) (O :: bits) = parseUInt size bits |> map (\(n, bits') => (Pos n, bits'))
parseSInt (S size) (I :: bits) = parseUInt size bits |> map (\(n, bits') => (negNat n, bits'))

parseChar : Parser Char
parseChar bits =
    parseUInt 16 bits  -- Idris' `Char`s are supposedly 2 bytes wide
        |> map (\(n, bits') => (chr (toIntNat n), bits'))

mutual
    parseVect : {n : Nat} -> (f : Format) -> Parser (Vect n (embed f))
    parseVect {n} f = rewrite plusCommutative Z n in go n []
        where
            go : {m : Nat} -> (n : Nat) -> Vect m (embed f) -> Parser (Vect (n + m) (embed f))
            go {m} Z acc bits = Just (reverse acc, bits)
            go {m} (S k) acc bits with (parse f bits)
                | Nothing = Nothing
                | Just (elem, bits'') =
                    rewrite plusSuccRightSucc k m in go k (elem :: acc) bits''

    ||| Interpret a binary format specification as a parser
    parse : %static (f : Format) -> Parser (embed f)
    parse FBad bits = Nothing
    parse FEnd bits = Just ((), bits)
    parse FBit bits = parseBit bits
    parse FChar bits = parseChar bits
    parse FU8 bits = parseUInt 8 bits
    parse FU16 bits = parseUInt 16 bits
    parse FU32 bits = parseUInt 32 bits
    parse FS8 bits = parseSInt 8 bits
    parse FS16 bits = parseSInt 16 bits
    parse FS32 bits = parseSInt 32 bits
    parse (FOffset offset f) bits with (tryDrop offset bits)
        | Nothing = Nothing
        | Just bits' = Just (Delay (parse f bits' |> map fst), bits)
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
    n <- FU16
    char ' '
    m <- FU16
    char '\n'
    bs <- FVect n (FVect m FBit)
    FEnd

||| Parse PBM data from a string of bits
parsePbm : Parser (embed BinaryFormats.pbm)
parsePbm = parse pbm


test : Format
test = do
    x <- FBit
    case x of
        O => FU8
        I => FS8
