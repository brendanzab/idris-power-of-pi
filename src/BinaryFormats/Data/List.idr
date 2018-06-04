module BinaryFormats.Data.List

%default total

export
trySplitAt : {a : Type} -> Nat -> List a -> Maybe (List a, List a)
trySplitAt offset bits =
    toMaybe (length bits < offset) (splitAt offset bits)

export
tryDrop : {a : Type} -> Nat -> List a -> Maybe (List a)
tryDrop offset bits =
    toMaybe (length bits < offset) (drop offset bits)
