{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--exact-data-cons" @-}
module NandComputer where

import Prelude hiding (map)

-- * Core types

data Bit = Zero | One

{-@ type Nat = {v:Int | v >= 0} @-}

{-@ measure invert @-}
invert :: Bit -> Bit
invert Zero = One
invert One = Zero

{-@ measure bitToBool @-}
bitToBool :: Bit -> Bool
bitToBool Zero = False
bitToBool One = True

{-@ measure bitToNat @-}
{-@ bitToNat :: _ -> Nat @-}
bitToNat :: Bit -> Int
bitToNat Zero = 0
bitToNat One = 1

{-@ measure bitVecToNat @-}
{-@ bitVecToNat :: _ -> Nat @-}
bitVecToNat :: [Bit] -> Int
bitVecToNat [] = 0
bitVecToNat (b:bs) = bitToNat b + 2 * bitVecToNat bs

-- * Utilities

{-@ reflect map @-}
map :: (a -> b) -> [a] -> [b]
map _ [] = []
map f (x:xs) = f x : map f xs

{-@ inline nand @-}
nand :: Bool -> Bool -> Bool
nand p q = not (p && q)

{-@ inline xor @-}
xor :: Bool -> Bool -> Bool
xor p q = (p && not q) || (q && not p)

-- * Basic logic gates

{-@ nandGate :: b0:_ -> b1:_ -> {v:_ | bitToBool v <=> nand (bitToBool b0) (bitToBool b1)} @-}
nandGate :: Bit -> Bit -> Bit
nandGate One One = Zero
nandGate _ _ = One

{-@ inverter :: b:_ -> {v:_ | bitToBool v <=> not (bitToBool b)} @-}
inverter :: Bit -> Bit
inverter b = nandGate b b

{-@ andGate :: b0:_ -> b1:_ -> {v:_ | bitToBool v <=> (bitToBool b0) && (bitToBool b1)} @-}
andGate :: Bit -> Bit -> Bit
andGate b0 b1 = inverter (nandGate b0 b1)

{-@ orGate :: b0:_ -> b1:_ -> {v:_ | bitToBool v <=> (bitToBool b0) || (bitToBool b1)} @-}
orGate :: Bit -> Bit -> Bit
orGate b0 b1 = nandGate (inverter b0) (inverter b1)

{-@ xorGate :: b0:_ -> b1:_ -> {v:_ | bitToBool v <=> xor (bitToBool b0) (bitToBool b1)} @-}
xorGate :: Bit -> Bit -> Bit
xorGate b0 b1 = let b2 = nandGate b0 b1 in nandGate (nandGate b0 b2) (nandGate b2 b1)

-- * Addition

{-@ halfAdder :: b0:_ -> b1:_ -> {v:_ | len v == 2 && bitVecToNat v == bitToNat b0 + bitToNat b1} @-}
halfAdder :: Bit -> Bit -> [Bit]
halfAdder b0 b1 = [xorGate b0 b1, andGate b0 b1]
{-@ automatic-instances halfAdder @-}

{-@ fullAdder :: b0:_ -> b1:_ -> c:_ -> {v:_ | len v == 2 && bitVecToNat v == bitToNat b0 + bitToNat b1 + bitToNat c} @-}
fullAdder :: Bit -> Bit -> Bit -> [Bit]
fullAdder b0 b1 c =
  let [l0, h0] = halfAdder b0 b1
      [l1, h1] = halfAdder l0 c in
    [l1, orGate h0 h1]
{-@ automatic-instances fullAdder @-}

{-@ nBitAdder :: as:_ -> {bs:_ | len as == len bs} -> c:_ -> {v:_ | len v == len as + 1 &&  bitVecToNat v == bitVecToNat as + bitVecToNat bs + bitToNat c} @-}
nBitAdder :: [Bit] -> [Bit] -> Bit -> [Bit]
nBitAdder [] [] c = [c]
nBitAdder (a:as) (b:bs) c =
  let [l, h] = fullAdder a b c in
    l:(nBitAdder as bs h)
nBitAdder _ _ _ = error "can't add bit vectors of different sizes"
{-@ automatic-instances nBitAdder @-}

{-@ zero :: n:Nat -> {v:_ | len v == n && bitVecToNat v == 0} @-}
zero :: Int -> [Bit]
zero 0 = []
zero n = Zero : zero (n - 1)
{-@ automatic-instances zero @-}

{-@ extend :: n:Nat -> bs:_ -> {v:_ | len v == len bs + n && bitVecToNat v == bitVecToNat bs} @-}
extend :: Int -> [Bit] -> [Bit]
extend n [] = zero n
extend n (b:bs) = b : extend n bs
{-@ automatic-instances extend @-}

{-@ one :: n:{_ | n > 0} -> {v:_ | len v == n && bitVecToNat v == 1} @-}
one :: Int -> [Bit]
one n = extend (n - 1) [One]
{-@ automatic-instances one @-}

{-@ incr :: bs:_ -> {v:_ | bitVecToNat v == bitVecToNat bs + 1} @-}
incr :: [Bit] -> [Bit]
incr [] = one 1
incr bs = nBitAdder bs (one (length bs)) Zero
{-@ automatic-instances incr @-}

-- * Inverter

{-@ nBitInverter :: bs:_ -> {v:_ | v == map invert bs}@-}
nBitInverter :: [Bit] -> [Bit]
nBitInverter [] = []
nBitInverter (b:bs) = inverter b : nBitInverter bs
{-@ automatic-instances nBitInverter @-}
