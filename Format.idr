module Format

import Data.Vect

data Bit = O | I
%name Bit b, b1, b2

data U = BIT | CHAR | NAT | VEC U Nat
%name U u

el : U -> Type
el BIT       = Bit
el CHAR      = Char
el NAT       = Nat
el (VEC u n) = Vect n (el u)

-- sh : t -> {auto pf : t = el u} -> String
-- sh x {pf = Refl} = ?shw_rhs_1

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
-- read u bs with (?toBytes)
  -- read u bs | with_pat = ?bs_rhs
-- read BIT (O::O::x::xs) = Just (x, xs)
-- read BIT xs = Nothing
-- read CHAR xs = ?read_rhs_2
-- read NAT xs = ?read_rhs_3
-- read (VEC x k) xs = ?read_rhs_4

mutual
  syntax "[[" [v] "]]" = val v
  syntax "⟦" [v] "⟧" = val v

  data Format : Type where
    Bad : Format
    End : Format
    Base : U -> Format
    Plus : Format -> Format -> Format
    Skip : Format -> Format -> Format
    -- Skip : (f : Format) -> val f -> Format -> Format
    Read : (f : Format) -> (⟦f⟧ -> Format) -> Format
  %name Format f, f1, f2

  val : Format -> Type
  val Bad = Void
  val End = Unit
  val (Base u)     = el u
  val (Plus f1 f2) = Either (val f1) (val f2)
  val (Skip _ f)   = val f
  val (Read f1 f2) = DPair (val f1) (\x => val (f2 x))

(>>) : Format -> Format -> Format
(>>) = Skip
-- f >> g = Skip f ?what g

(>>=) : (f : Format) -> (⟦f⟧ -> Format) -> Format
(>>=) = Read

satisfy : (f : Format) -> (⟦f⟧ -> Bool) -> Format
satisfy f pred = Read f $ \x => if pred x then End else Bad

char : Char -> Format
char c = satisfy (Base CHAR) (== c)
-- char c = Read (Base CHAR) $ \c' => if c == c' then End else Bad

pbm : Format
pbm = do
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
parse (Skip f1 f2) bs with (parse f1 bs)
  parse (Skip f1 f2) bs | Nothing      = Nothing
  parse (Skip f1 f2) bs | Just (_, cs) = parse f2 cs
parse (Read f1 f2) bs with (parse f1 bs)
  parse (Read f1 f2) bs | Nothing      = Nothing
  parse (Read f1 f2) bs | Just (x, cs) with (parse (f2 x) cs)
    parse (Read f1 f2) bs | Just (x, cs) | Nothing      = Nothing
    parse (Read f1 f2) bs | Just (x, cs) | Just (y, ds) = Just ((x ** y), ds)

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
