module BinaryFormats.Data.Bit

%default total

||| A binary digit (either 0 or 1)
public export
data Bit : Type where
    ||| The 0 bit
    O : Bit
    ||| The 1 bit
    I : Bit

implementation Num Bit where
    (+) O O = O
    (+) O I = I
    (+) I O = I
    (+) I I = I

    (*) O O = O
    (*) O I = O
    (*) I O = O
    (*) I I = I

    fromInteger n = if n > 0 then I else O
