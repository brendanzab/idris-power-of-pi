module BinaryFormats.Data.Bit

%default total

||| A binary digit (either 0 or 1)
public export
data Bit : Type where
    ||| The 0 digit
    O : Bit
    ||| The 1 digit
    I : Bit
