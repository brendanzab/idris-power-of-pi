module BinaryFormats

import Control.Pipeline
import Data.Vect

import BinaryFormats.Data.Bit
import BinaryFormats.Data.List

%default total


--------------------------------------------------------------------------------
-- Core
--------------------------------------------------------------------------------

||| A universe of binary data formats
public export
data Format : Type -> Type where
    FFail : Format a
    FBit : Format Bit
    FPure : a -> Format a
    FRef : Format (List Bit)
    FPtr : Nat -> List Bit -> Format a -> Format (Lazy (Maybe a))
    FVect : (size : Nat) -> Format a -> Format (Vect size a)
    FPlus : Format a -> Format b -> Format (Either a b)
    FBind : Format a -> (a -> Format b) -> Format b


-- DSL constructors

export
fail : Format a
fail = FFail

export
bit : Format Bit
bit = FBit

export
ref : Format (List Bit)
ref = FRef

export
ptr : Nat -> List Bit -> Format a -> Format (Lazy (Maybe a))
ptr = FPtr

export
vect : (size : Nat) -> Format a -> Format (Vect size a)
vect = FVect

export
implementation Functor Format where
    map f x = FBind x (FPure . f)

export
implementation Applicative Format where
    pure = FPure
    (<*>) f x = FBind f (\f => FBind x (\x => FPure (f x)))

export
implementation Monad Format where
    (>>=) = FBind


--------------------------------------------------------------------------------
-- Derived formats
--------------------------------------------------------------------------------

||| The byte-order of the datatype
public export
data Endianness : Type where
    Le : Endianness
    Be : Endianness


-- Helper functions

unsignedBits : Num a => Nat -> Format a
unsignedBits size =
    vect size bit |> map (go 0)

    where
        go : Num a => a -> Vect n Bit -> a
        go acc [] = acc
        go acc (O :: bits) = go (2 * acc) bits
        go acc (I :: bits) = go (1 + (2 * acc)) bits

unsignedBytes : Num a => Nat -> Endianness -> Format a
unsignedBytes size endianness =
    unsignedBits (size * 8) -- FIXME: Use endianness


-- Datatypes

export
b8 : Format Bits8
b8 = unsignedBits 8

export
b16 : Format Bits16
b16 = unsignedBits 16

export
b32 : Format Bits32
b32 = unsignedBits 32

export
b64 : Format Bits64
b64 = unsignedBits 64

export
u8 : Format Nat
u8 = unsignedBits 8

export
u16 : Endianness -> Format Nat
u16 = unsignedBytes 2

export
u24 : Endianness -> Format Nat
u24 = unsignedBytes 3

export
u32 : Endianness -> Format Nat
u32 = unsignedBytes 4

export
u64 : Endianness -> Format Nat
u64 = unsignedBytes 8

export
char16 : Format Char
char16 = u16 Be |> map (chr . toIntNat) -- Idris' `Char`s are supposedly 2 bytes wide :/


-- Predicates

||| Require a predicate to be satisfied
export
satisfy : Format a -> (a -> Bool) -> Format ()
satisfy f pred =
    f >>= (\x => if pred x then pure () else fail)

export
isChar16 : Char -> Format ()
isChar16 ch = satisfy char16 ((==) ch)


--------------------------------------------------------------------------------
-- Parsing
--------------------------------------------------------------------------------

export
Parser : Type -> Type
Parser a = (bits : List Bit) -> Maybe (a, List Bit)

||| Interpret a binary format specification as a parser
export
parse : (f : Format a) -> Parser a
parse FFail bits = Nothing
parse FBit [] = Nothing
parse FBit (bit :: bits) = Just (bit, bits)
parse (FPure value) bits = Just (value, bits)
parse FRef bits = Just (bits, bits)
parse (FPtr {a} offset refBits f) bits with (tryDrop offset refBits)
    | Nothing = Nothing
    | Just refBits' = Just (Delay (parse {a} f refBits' |> map fst), bits)
parse (FVect n f) bits =
    rewrite plusCommutative Z n in parseVect n f [] bits
    where
        parseVect : {m : Nat} -> (n : Nat) -> (f : Format a) -> Vect m a -> Parser (Vect (n + m) a)
        parseVect {a} {m} Z f acc bits = Just (reverse acc, bits)
        parseVect {a} {m} (S k) f acc bits with (parse {a} f bits)
            | Nothing = Nothing
            | Just (elem, bits') =
                rewrite plusSuccRightSucc k m in parseVect k f (elem :: acc) bits'
parse (FPlus {a} {b} f1 f2) bits with (parse {a} f1 bits)
    | (Just (x, bits')) = Just (Left x, bits')
    | Nothing with (parse {a = b} f2 bits)
        | (Just (y, bits')) = Just (Right y, bits')
        | Nothing = Nothing
parse (FBind {a} {b} f1 f2) bits with (parse {a} f1 bits)
    | Nothing = Nothing
    | (Just (x, bits')) with (parse {a = b} (f2 x) bits')
        | Nothing = Nothing
        | Just (y, bits'') = Just (y, bits'')


--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

record Pbm where
    constructor MkPbm
    width : Nat
    height : Nat
    imageData : Vect width (Vect height Bit)

||| PBM binary format
pbm : Format Pbm
pbm = do
    isChar16 'p'
    isChar16 '4'
    isChar16 ' '
    width <- u16 Le
    isChar16 ' '
    height <- u16 Le
    isChar16 '\n'
    imageData <- vect width (vect height bit)
    pure (MkPbm width height imageData)

record Bitmap where
    constructor MkBitmap
    width : Nat
    height : Nat
    imageData : Vect (width * height) Nat

bitmap : Format Bitmap
bitmap = do
    width <- u16 Le
    height <- u16 Le
    imageData <- vect (width * height) u8
    pure (MkBitmap width height imageData)
