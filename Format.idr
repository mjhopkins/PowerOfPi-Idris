module Format

import Data.Vect
import Data.String

data Bit = O | I
%name Bit b, b1, b2

data U = BIT | CHAR | NAT | VEC U Nat
%name U u

Eq U where
  BIT == BIT   = True
  CHAR == CHAR = True
  NAT == NAT   = True
  (VEC u n) == (VEC v m) = u == v && n == m
  _ == _ = False

el : U -> Type
el BIT       = Bit
el CHAR      = Char
el NAT       = Nat
el (VEC u n) = Vect n (el u)

eqEl : {u : U} -> el u -> el u -> Bool
eqEl {u = BIT} x y = ?eqEl_rhs_1
eqEl {u = CHAR} x y = ?eqEl_rhs_2
eqEl {u = NAT} x y = ?eqEl_rhs_3
eqEl {u = (VEC u k)} x y = ?eqEl_rhs_4

parens : String -> String
parens str = "(" ++ str ++ ")"

shw : el u -> String
shw {u = BIT} O        = "0"
shw {u = BIT} I        = "1"
shw {u = CHAR} c       = cast c
shw {u = NAT} Z        = "Zero"
shw {u = NAT} (S k)    = "Succ " ++ shw {u = NAT} k
shw {u = (VEC v Z)} [] = "[]"
shw {u = (VEC v (S len))} (x :: xs)
  = parens (shw {u = v} x) ++ " :: " ++ parens (shw {u = VEC v len} xs)

read : (u : U) -> List Bit -> Maybe (el u, List Bit)

mutual
  syntax "[[" [v] "]]" = val v
  syntax "⟦" [v] "⟧" = val v

  data Format : Type where
    Bad : Format
    End : Format
    Base : U -> Format
    Plus : Format -> Format -> Format
    -- Skip : Format -> Format -> Format
    Skip : (f : Format) -> ⟦f⟧ -> Format -> Format
    Read : (f : Format) -> (⟦f⟧ -> Format) -> Format
  %name Format f, f1, f2

  val : Format -> Type
  val Bad = Void
  val End = Unit
  val (Base u)     = el u
  val (Plus f1 f2) = Either (val f1) (val f2)
  -- val (Skip _ f)   = val f
  val (Skip _ _ f) = val f
  val (Read f1 f2) = DPair (val f1) (\x => val (f2 x))

mutual
  eqF : Format -> Format -> Bool
  eqF Bad Bad = True
  eqF End End = True
  eqF (Base u) (Base v) = u == v
  eqF (Plus l1 r1) (Plus l2 r2) = eqF l1 l2 && eqF r1 r2
  eqF (Skip l1 v1 r1) (Skip l2 v2 r2) = eqF l1 l2 && eqF r1 r2 && eq' v1 v2


  eq' : {f : Format} -> {g : Format} -> ⟦f⟧ -> ⟦g⟧ -> Bool
  eq' {f} {g} x y with (eqF f g)
    eq' {f = f} {g = g} x y | False = False
    eq' {f = f} {g = g} x y | True = ?x_rhs_2

  eq : {f : Format} -> ⟦f⟧ -> ⟦f⟧ -> Bool
  eq {f = End} () () = True
  eq {f = (Base u)} x y     = eqEl x y
  eq {f = (Plus f g)} x y   = eq x y
  eq {f = (Skip f v g)} x y = eq x y
  -- eq {f = (Read f g)} (x1 ** x2) (y1 ** y2) = eq x1 y1 && ?what x2 y2
  eq {f = (Read f g)} (l1 ** r1) (l2 ** r2) with (eq l1 l2)
    eq {f = (Read f g)} (l1 ** r1) (l2 ** r2) | False = False
    eq {f = (Read f g)} (l1 ** r1) (l2 ** r2) | True = (?something)
    -- eq {f = (Read f g)} (l1 ** r1) (l2 ** r2) | True with (?someeq (g l1) (g l2))
      -- eq {f = (Read f g)} (l1 ** r1) (l2 ** r2) | True | with_pat = ?r2_rhs

Eq Format where
  Bad == Bad = True
  End == End = True
  (Base u) == (Base v) = u == v
  (Plus l1 r1)    == (Plus l2 r2)    = l1 == l2 && r1 == r2
  -- (Skip f1 v1 r1) == (Skip f2 v2 r2) = f1 == f2 && r1 == r2
  -- (Skip l1 v1 r1) == (Skip l2 v2 r2) with (_)
    -- (Skip l1 v1 r1) == (Skip l2 v2 r2) | with_pat = ?r2_rhs
  (Skip l1 v1 r1) == (Skip l2 v2 r2) = l1 == l2 && r1 == r2 && ?what v1 v2

infixl 7 >>
-- (>>) : (f : Format) -> Format -> Format
(>>) : (f : Format) -> ⟦f⟧ -> Format -> Format
(>>) = Skip

infixl 1 >>=
(>>=) : (f : Format) -> (⟦f⟧ -> Format) -> Format
(>>=) = Read

(||) : Format -> Format -> Format
(||) = Plus

satisfy : (f : Format) -> (⟦f⟧ -> Bool) -> Format
satisfy f pred = Read f $ \x => if pred x then End else Bad

char' : Char -> Format
char' c = Read (Base CHAR) $ \c' => if c == c' then End else Bad

char : Char -> Format
char c = satisfy (Base CHAR) (== c)

pbm : Format
pbm =
  (>>) (char 'P') ('P' ** ())
    ( (>>) (char '4') ('4' ** ())
      ( (>>) (char ' ') (' ' ** ())
        ( (>>=) (Base NAT)
          (\n =>
            ( (>>) (char ' ') (' ' ** ())
              ( (>>=) (Base NAT)
                (\m =>
                  ( (>>=) (Base (VEC (VEC BIT m) n))
                    (\vs =>
                      End
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

pbm'' : Format
pbm'' =
  (>>) (char 'P') ('P' ** ()) $
  (>>) (char '4') ('4' ** ()) $
  (>>) (char ' ') (' ' ** ()) $
  (>>=) (Base NAT) $ \n =>
  (>>) (char ' ') (' ' ** ()) $
  (>>=) (Base NAT) $ \m =>
  (>>) (char '\n') ('\n' ** ()) $
  (>>=) (Base (VEC (VEC BIT m) n)) $ \vs =>
  End

-- pbm'' : Format
-- pbm'' =
--       (>>) (char 'P') ('P' ** ())
--     $ (>>) (char '4') ('4' ** ())
--     $ (>>) (char ' ') (' ' ** ())
--     $ (>>=) (Base NAT)
--     $ \n =>
--       (>>) (char ' ') (' ' ** ())
--     $ (>>=) (Base NAT)
--     $ \m =>
--       (>>=) (Base (VEC (VEC BIT m) n))
--     $ \vs =>
--       End

pbm' : Format
pbm' = do
  char 'P'
  char '4'
  char ' '
  n <- Base NAT
  char ' '
  m <- Base NAT
  char '\n'
  bs <- Base (VEC (VEC BIT m) n)
  End

parse : (f : Format) -> List Bit -> Maybe (⟦f⟧, List Bit)
parse Bad bs          = Nothing
parse End bs          = Just ((), bs)
parse (Base u) bs     = read u bs
parse (Plus f1 f2) bs with (parse f1 bs)
  parse (Plus f1 f2) bs | Just (x, cs) = Just (Left x, cs)
  parse (Plus f1 f2) bs | Nothing with (parse f2 bs)
    parse (Plus f1 f2) bs | Nothing | Just (y, ds) = Just (Right y, ds)
    parse (Plus f1 f2) bs | Nothing | Nothing      = Nothing
-- parse (Skip f1 f2) bs with (parse f1 bs)
-- parse (Skip f1 v f2) bs | Nothing      = Nothing
-- parse (Skip f1 v f2) bs | Just (_, cs) = parse f2 cs
parse (Skip f1 v f2) bs with (parse f1 bs)
  parse (Skip f1 v f2) bs | Nothing  = Nothing
  parse (Skip f1 v f2) bs | Just (v', cs) with (Format.eq v v')
    parse (Skip f1 v f2) bs | Just (v', cs) | False = Nothing
    parse (Skip f1 v f2) bs | Just (v', cs) | True = parse f2 cs
parse (Read f1 f2) bs with (parse f1 bs)
  parse (Read f1 f2) bs | Nothing      = Nothing
  parse (Read f1 f2) bs | Just (x, cs) with (parse (f2 x) cs)
    parse (Read f1 f2) bs | Just (x, cs) | Nothing      = Nothing
    parse (Read f1 f2) bs | Just (x, cs) | Just (y, ds) = Just ((x ** y), ds)

charToNat : Char -> Maybe Nat
charToNat '0' = Just 0
charToNat '1' = Just 1
charToNat '2' = Just 2
charToNat '3' = Just 3
charToNat '4' = Just 4
charToNat '5' = Just 5
charToNat '6' = Just 6
charToNat '7' = Just 7
charToNat '8' = Just 8
charToNat '9' = Just 9
charToNat _   = Nothing

parseNat : List Char -> Maybe (Nat, List Char)
parseNat [] = Nothing
parseNat (c :: cs) with (charToNat c)
  parseNat (c :: cs) | Nothing = Nothing
  parseNat (c :: cs) | Just n  with (parseNat cs)
    parseNat (c :: cs) | Just n  | Nothing      = Just (n, cs)
    parseNat (c :: cs) | Just n  | Just (m, ds) = Just ((power 10 (length (show m))) * n + m, ds)

readStr : (u : U) -> List Char -> Maybe (el u, List Char)
readStr BIT ('I'::cs)    = Just (I, cs)
readStr BIT ('O'::cs)    = Just (O, cs)
readStr BIT cs           = Nothing
readStr CHAR (c::cs)     = Just (c, cs)
readStr CHAR Nil         = Nothing
readStr NAT xs           = parseNat xs
readStr (VEC u Z) xs     = Just (Nil, xs)
readStr (VEC u (S k)) xs with (readStr u xs)
  readStr (VEC u (S k)) xs | Nothing      = Nothing
  readStr (VEC u (S k)) xs | Just (a, ds) with (readStr (VEC u k) ds)
    readStr (VEC u (S k)) xs | Just (a, ds) | Nothing      = Nothing
    readStr (VEC u (S k)) xs | Just (a, ds) | Just (vec, es) =
      rewrite plusCommutative 1 k in Just (vec ++ [a], es)

parseStr : (f : Format) -> List Char -> Maybe (⟦f⟧, List Char)
parseStr Bad bs          = Nothing
parseStr End bs          = Just ((), bs)
parseStr (Base u) bs     = readStr u bs
parseStr (Plus f1 f2) bs with (parseStr f1 bs)
  parseStr (Plus f1 f2) bs | Just (x, cs) = Just (Left x, cs)
  parseStr (Plus f1 f2) bs | Nothing with (parseStr f2 bs)
    parseStr (Plus f1 f2) bs | Nothing | Just (y, ds) = Just (Right y, ds)
    parseStr (Plus f1 f2) bs | Nothing | Nothing      = Nothing
parseStr (Skip f1 v f2) bs with (parseStr f1 bs)
  parseStr (Skip f1 v f2) bs | Nothing  = Nothing
  parseStr (Skip f1 v f2) bs | Just (v', cs) with (Format.eq v v')
    parseStr (Skip f1 v f2) bs | Just (v', cs) | False = Nothing
    parseStr (Skip f1 v f2) bs | Just (v', cs) | True = parseStr f2 cs
parseStr (Read f1 f2) bs with (parseStr f1 bs)
  parseStr (Read f1 f2) bs | Nothing      = Nothing
  parseStr (Read f1 f2) bs | Just (x, cs) with (parseStr (f2 x) cs)
    parseStr (Read f1 f2) bs | Just (x, cs) | Nothing      = Nothing
    parseStr (Read f1 f2) bs | Just (x, cs) | Just (y, ds) = Just ((x ** y), ds)

elUToStr : el u -> String
elUToStr {u = BIT} O  = "O"
elUToStr {u = BIT} I  = "I"
elUToStr {u = CHAR} c = cast c
elUToStr {u = NAT} n  = show n
elUToStr {u = VEC u Z} []    = ""
elUToStr {u = VEC u (S k)} (x :: xs) = elUToStr x ++ elUToStr {u = VEC u k} xs

printStr : (f : Format) -> ⟦f⟧ -> String
printStr End ()               = ""
printStr (Base u) x           = elUToStr x
printStr (Plus f g) (Left l)  = printStr f l
printStr (Plus f g) (Right r) = printStr g r
printStr (Skip f v g) x       = printStr f v ++ printStr g x
printStr (Read f g) (x ** y)  = printStr f x ++ printStr (g x) y

v : Vect 4 (Vect 1 Bit)
v = [[I],[O],[I],[O]]

-- > val pbm
-- (x : Nat ** x1 : Nat ** x2 : Vect x (Vect x1 Bit) ** ()) : Type

printV : String
printV = printStr pbm'' $ (4 ** 1 ** v ** ())

-- toBits : String -> List Bit
-- toBits s = foldl (\bits => \ch => enc ch ++ bits) [] (the (List Char) (cast s))
--   where
--     enc = toBin . ord
--
--     toBin : Int -> List Bit
--     toBin 0 = []
--     toBin n with (mod n 2)
--       toBin n  | 0 = O :: toBin (div n 2)
--       toBin n  | 1 = I :: toBin (div n 2)
--
--
-- print : (f : Format) -> ⟦f⟧ -> List Bit
-- print End ()                 = []
-- print (Base u) x             = toBits (shw x)
-- print (Plus f1 f2) (Left l)  = print f1 l
-- print (Plus f1 f2) (Right r) = print f2 r
-- print (Skip f1 v f2) x       = print f1 v ++ print f2 x
-- print (Read f1 f2) (x ** y)  = print f1 x ++ print (f2 x) y
