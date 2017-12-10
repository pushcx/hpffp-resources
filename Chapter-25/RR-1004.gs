------------------------------------------------------------------------------
-- Composing monads                                  Thursday December 2, 1993
--
-- The definitions in this script are intended to be used with Gofer 2.28
-- and the standard Gofer prelude.  These definitions provide a very close,
-- complete, executable implementation of the constructions described in the
-- report:
--
--     Composing Monads   by  Mark P. Jones and Luc Duponcheel
--     Yale University Research Report YALEU/DCS/RR-1004
--     December 1993
--     (Available by anonymous ftp from nebula.cs.yale.edu
--     in the directory pub/yale-fp/reports).
--
-- To avoid conflicts with the standard.prelude, we use the name `fun' rather
-- than the name `map' which is used in the paper.
------------------------------------------------------------------------------

-- Start with some hacks to express `laws' -----------------------------------

infix 1 ===

data Law a = Unspecified

(===)   :: a -> a -> Law a
x === y  = error "uncomputable equality"


-- Functors ------------------------------------------------------------------

class Functor f where
    fun :: (a -> b) -> (f a -> f b)

law1      :: Functor f => Law (f a -> f a)
law1       = fun id === id

law2      :: Functor f => (b -> c) -> (a -> b) -> Law (f a -> f c)
law2 f g   = fun f . fun g === fun (f . g)


-- Premonads -----------------------------------------------------------------

class Functor m => Premonad m where
    unit :: a -> m a

law3      :: Premonad m => (a -> b) -> Law (a -> m b)
law3 f     = fun f . unit  ===  unit . f


-- Monads --------------------------------------------------------------------

class Premonad m => Monad m where
    join :: m (m a) -> m a

law4       :: Monad m => (a -> b) -> Law (m (m a) -> m b)
law4 f      = join . fun (fun f) === fun f . join

law5       :: Monad m => Law (m a -> m a)
law5        = join . unit === id

law6       :: Monad m => Law (m a -> m a)
law6        = join . fun unit === id

law7       :: Monad m => Law (m (m (m a)) -> m a)
law7        = join . fun join === join . join


-- General framework for composition constructions ---------------------------

class Composer c where
    open  :: c f g x -> f (g x)
    close :: f (g x) -> c f g x

funC :: (Functor f, Functor g) => (a -> b) -> (f (g a) -> f (g b))
funC  = fun . fun

instance (Composer c, Functor f, Functor g) => Functor (c f g) where
    fun f = close . funC f . open

unitC :: (Premonad m, Premonad n) => a -> m (n a)
unitC  = unit . unit

instance (Composer c, Premonad m, Premonad n) => Premonad (c m n) where
    unit = close . unitC

wrap  :: (Composer c, Functor m, Functor n) =>
           (m (n (m (n a))) -> m (n a)) ->
             (c m n (c m n a) -> c m n a)
wrap j = close . j . funC open . open

right :: (Composer c, Premonad f) => g a -> c f g a
right  = close . unit

left  :: (Composer c, Functor f, Premonad g) => f a -> c f g a
left   = close . fun unit


-- The prod construction -----------------------------------------------------

data PComp f g x = PC (f (g x))

instance Composer PComp where
    open (PC x) = x
    close       = PC

class (Monad m, Premonad n) => PComposable m n where
    prod :: n (m (n a)) -> m (n a)

joinP :: (PComposable m n) => m (n (m (n a))) -> m (n a)
joinP  = join . fun prod

p1 f   =  prod . fun (funC f) === funC f . prod
p2 ()  =  prod . unit         === id
p3 ()  =  prod . fun unitC    === unit
p4 ()  =  prod . fun joinP    === joinP . prod

instance PComposable m n => Monad (PComp m n) where
    join = wrap joinP


-- The dorp construction -----------------------------------------------------

data DComp f g x = DC (f (g x))

instance Composer DComp where
    open (DC x) = x
    close       = DC

class (Premonad m, Monad n) => DComposable m n where
    dorp :: m (n (m a)) -> m (n a)

joinD :: (DComposable m n) => m (n (m (n a))) -> m (n a)
joinD  = fun join . dorp

d1 f   =  dorp . funC (fun f) === funC f . dorp
d2 ()  =  dorp . unitC        === fun unit
d3 ()  =  dorp . funC unit    === id
d4 ()  =  dorp . joinD        === joinD . funC dorp

instance (DComposable m n) => Monad (DComp m n) where
    join = wrap joinD


-- The swap construction -----------------------------------------------------

data SComp f g x = SC (f (g x))

instance Composer SComp where
    open (SC x) = x
    close       = SC

class (Monad m, Monad n) => SComposable m n where
    swap :: n (m a) -> m (n a)

joinS :: (SComposable m n) => m (n (m (n a))) -> m (n a)
joinS  = fun join . join . fun swap

s1 f   =  swap . funC f   === funC f . swap
s2 ()  =  swap . unit     === fun unit
s3 ()  =  swap . fun unit === unit
s4 ()  =  prod . fun dorp === dorp . prod
          where prod = fun join . swap
                dorp = join . fun swap

instance (SComposable m n) => Monad (SComp m n) where
    join = wrap joinS


-- Deriving prod and dorp from swap ------------------------------------------

instance (SComposable m n) => PComposable m n where
    prod = fun join . swap

instance (SComposable m n) => DComposable m n where
    dorp = join . fun swap


-- The Maybe monad -----------------------------------------------------------

data Maybe a = Just a | Nothing

instance Functor Maybe where
    fun f (Just x) = Just (f x)
    fun f Nothing  = Nothing

instance Premonad Maybe where
    unit = Just

instance Monad Maybe where
    join (Just x) = x
    join Nothing  = Nothing

instance PComposable m Maybe where
    prod (Just m) = m
    prod Nothing  = unit Nothing


-- Reader monads -------------------------------------------------------------

-- The (r->) syntax for readers is supported in Gofer 2.28c (not released
-- at the time of writing), but not in Gofer 2.28b, so we use ((->)r) instead.

instance Functor ((->)r) where
    fun f x = f . x

instance Premonad ((->)r) where
    unit x y = x

instance Monad ((->)r) where
    join f x = f x x

instance DComposable ((->)r) n where
    dorp f r = f r `bind` \g -> unit (g r)
          -- = [ g r | g <- f r ]

-- Gofer only supports the monad comprehension notation when the cc.prelude
-- is used.  Since we intend this program to be used with the standard.prelude,
-- we have rewritten the monad comprehensions given in the paper using the
-- bind function defined:

bind      :: Monad m => m a -> (a -> m b) -> m b
x `bind` f = join (fun f x)

-- See Wadler's paper on the Essence of Functional Programming for further
-- information about bind.


-- The List monad ------------------------------------------------------------

instance Functor [] where
    fun f xs = [ f x | x<-xs ]

instance Premonad [] where
    unit x = [x]

instance Monad [] where
    join xss = [ x | xs<-xss, x<-xs ]

instance SComposable m [] where
    swap []     = unit []
    swap (x:xs) = x       `bind` \y  ->
                  swap xs `bind` \ys ->
                  unit (y:ys)
             -- = [ y:ys | y<-x, ys<-swap xs ]


-- Writer monads -------------------------------------------------------------

-- A brief interlude into the realms of monoids:

class Monoid s where
    zero :: s
    add  :: s -> s -> s

instance Monoid [a] where
    zero   = []
    add    = (++)

instance Monoid (a -> a) where
    zero = id
    add  = (.)

-- Now back to monads:

data Writer s a = Result s a

instance Functor (Writer s) where
    fun f (Result s a) = Result s (f a)

instance Monoid s => Premonad (Writer s) where
    unit = Result zero

write    :: s -> Writer s ()
write msg = Result msg ()

instance Monoid s => Monad (Writer s) where
    join (Result s (Result t x)) = Result (add s t) x

-- Proof that (Writer s) is a monad, given that s is a monoid:
-- 
-- (1), (2), (3): trivial!
-- 
-- (4):  join (map (map f) (Result s (Result t x)))
--     = join (Result s (map f (Result t x)))
--     = join (Result s (Result t (f x)))
--     = Result (add s t) (f x)
--     = map f (Result (add s t) x)
--     = map f (join (Result s (Result t x)))
-- 
-- (5):  join (unit (Result t x))
--     = join (Result zero (Result t x))
--     = Result (add zero t) x
--     = Result t x                           (left identity)
-- 
-- (6):  join (map unit (Result t x))
--     = join (Result t (unit x))
--     = join (Result t (Result zero x))
--     = Result (add t zero) x
--     = Result t x                           (right identity)
-- 
-- (7):  join (map join (Result s (Result t (Result u x))))
--     = join (Result s (join (Result t (Result u x))))
--     = join (Result s (Result (add t u) x))
--     = Result (add s (add t u)) x
--     = Result (add (add s t) u) x           (associativity)
--     = join (Result (add s t) (Result u x))
--     = join (join (Result s (Result t (Result u x))))

instance Monoid s => SComposable m (Writer s) where
    swap (Result s ma) = ma `bind` \a -> unit (Result s a)
                    -- = [ Result s a | a <- ma ]

-- Proof that writers compose with arbitrary monads is not included
-- in the report.  An outline of the proof is sketched below:
--
-- S(1):  swap (map (map f) (Result s ma))
--      = swap (Result s (map f ma))
--      = [ Result s a | a <- map f ma ]
--      = [ Result s (f a) | a <- ma ]
--      = [ map f (Result s a) | a <- ma ]
--      = map (map f) [ Result s a | a <- ma ]
--      = map (map f) (swap (Result s ma))
--
-- S(2):  swap (unit ma)
--      = swap (Result zero ma)
--      = [ Result zero a | a <- ma ]
--      = map (Result zero) [ a | a <- ma ]
--      = map unit ma
--
-- S(3):  swap (map unit (Result s ma))
--      = swap (Result s (unit ma))
--      = [ Result s a | a <- unit ma ]
--      = [ Result s ma ]
--      = unit (Result s ma)
--
-- S(4): Preliminary calculations and lemmas:
--
-- prod (Result s ma)
--  = map join (swap (Result s ma))
--  = map join [ Result s a | a<-ma ]
--  = [ join (Result s a) | a <- ma ]
--
-- CLAIM:
--   swap (join (Result s as)) = [ join (Result s a) | a <- swap as ]
-- i.e.
--   swap . join . Result s    = map (join . Result s) . swap
--
-- swap (join (Result s (Result t ma)))
--  = swap (Result (add s t) ma)
--  = [ Result (add s t) a | a <- ma ]
--  = [ join (Result s (Result t a)) | a <- ma ]
--  = map (join . Result s) [ Result t a | a <- ma ]
--  = map (join . Result s) (swap ma)
--
-- S(4):  prod (map dorp (Result s ma))
--      = prod (Result s (dorp ma))
--      = [ join (Result s a) | a <- dorp ma ]
--      = [ join (Result s a) | a <- join (map swap ma) ]
--      = [ join (Result s a) | as <- map swap ma, a <- as ]
--      = [ join (Result s a) | as <- ma, a <- swap as ]
--      = join [ [ join (Result s a) | a <- swap as ] | as <- ma]
--      = join [ swap (join (Result s as)) | as <- ma ]
--      = join (map swap [ join (Result s as) | as <- ma ])
--      = dorp [ join (Result s as) | as <- ma ]
--      = dorp (prod (Result s ma))


-- The Error monad -----------------------------------------------------------

data Error a = Ok a | Error String

instance Functor Error where
    fun f (Ok x)      = Ok (f x)
    fun f (Error msg) = Error msg

instance Premonad Error where
    unit = Ok

instance Monad Error where
    join (Ok x)      = x
    join (Error msg) = Error msg

instance SComposable m Error where
    swap (Ok m)      = fun Ok m
    swap (Error msg) = unit (Error msg)


-- The Tree monad ------------------------------------------------------------

data Tree a = Leaf a  |  Tree a :^: Tree a

instance Functor Tree where
    fun f (Leaf x)  = Leaf (f x)
    fun f (l :^: r) = fun f l :^: fun f r

instance Premonad Tree where
    unit = Leaf

instance Monad Tree where
    join (Leaf m)  = m
    join (l :^: r) = join l :^: join r

instance SComposable m Tree where
    swap (Leaf m)  = fun Leaf m
    swap (l :^: r) = swap l           `bind` \sl ->
                     swap r           `bind` \sr ->
                     unit (sl :^: sr)
                -- = [ sl :^: sr | sl <- swap l, sr <- r ]

-- S(1):  swap (map (map f) (Leaf m))
--      = swap (Leaf (map f m))
--      = map Leaf (map f m)
--      = map Leaf [ f x | x <- m ]
--      = [ Leaf (f x) | x <- m ]
--      = [ map f (Leaf x) | x <- m ]
--      = map (map f) [ Leaf x | x <- m ]
--      = map (map f) (swap (Leaf m))
--
--        swap (map (map f) (l :^: r))
--      = swap (map (map f) l :^: map (map f) r)
--      = [ sl :^: sr | sl<-swap (map (map f) l), sr<-swap (map (map f) r) ]
--      = [ sl :^: sr | sl<-map (map f) (swap l), sr<-map (map f) (swap r) ]
--      = [ map f sl :^: map f sr | sl <- swap l, sr <- swap r ]
--      = [ map f (sl :^: sr) | sl <- swap l, sr <- swap r ]
--      = map (map f) [ sl :^: sr | sl <- swap l, sr <- swap r ]
--      = map (map f) (swap (l :^: r))
--
-- S(2):  swap (unit x)
--      = swap (Leaf x)
--      = map Leaf x
--      = map unit x
--
-- S(3):  swap (map unit (Leaf x))
--      = swap (Leaf (unit x))
--      = map Leaf (unit x)
--      = unit (Leaf x)
--
--        swap (map unit (l :^: r))
--      = swap (map unit l :^: map unit r)
--      = [ sl :^: sr | sl <- swap (map unit l), sr <- swap (map unit r) ]
--      = [ sl :^: sr | sl <- unit l, sr <- unit r ]
--      = [ l :^: r ]
--      = unit (l :^: r)
--
-- S(4): Preliminaries
-- prod = map join . swap
-- dorp = join . map swap
--
-- prod (Leaf m)
--  = map join (swap (Leaf m))
--  = map join [ Leaf x | x <- m ]
--  = [ join (Leaf x) | x <- m ]
--  = [ x | x <- m]
--  = m
--
-- prod (l :^: r)
--  = map join [ sl :^: sr | sl <- swap l, sr <- swap r ]
--  = [ join (sl :^: sr) | sl <- swap l, sr <- swap r ]
--  = [ join sl :^: join sr | sl <- swap l, sr <- swap r ]
--  = [ pl :^: pr | pl <- map join (swap l), pr <- map join (swap r) ]
--  = [ pl :^: pr | pl <- prod l, pr <- prod r ]
--
-- S(4):  prod (map dorp (Leaf x))
--      = prod (Leaf (dorp x))
--      = dorp x
--      = dorp (prod (Leaf x))
--
--        prod (map dorp (l :^: r))
--      = prod (map dorp l :^: map dorp r)
--      = [ sl :^: sr | sl <- prod (map dorp l), sr <- prod (map dorp r) ]
--      = [ sl :^: sr | sl <- dorp (prod l), sr <- dorp (prod r) ]
--      = [ sl :^: sr | sl <- join (map swap (prod l)),
--                      sr <- join (map swap (prod r)) ]
--      = [ sl :^: sr | pl <- map swap (prod l), sl <- pl,
--                      pr <- map swap (prod r), sr <- pr ]
--      = [ sl :^: sr | pl <- map swap (prod l), pr <- map swap (prod r),
--                      sl <- pl, sr <- pr ]
--      = [ sl :^: sr | pl<-prod l, pr<-prod r, sl<-swap pl, sr<-swap pr ]
--      = join [ [ sl :^: sr | sl <- swap pl, sr <- swap pr ]
--              | pl <- prod l, pr <- prod r ]
--      = join [ swap (pl :^: pr) | pl <- prod l, pr <- prod r ]
--      = join (map swap [ pl :^: pr | pl <- prod l, pr <- prod r ])
--      = dorp [ pl :^: pr | pl <- prod l, pr <- prod r ]
--      = dorp (prod (l :^: r))


-- An expression evaluator ---------------------------------------------------

type Value = Int
type Name  = String
type Env   = [(Name,Value)]

data Expr  = Const Value | Var Name | Expr :+: Expr | Trace String Expr

type M a = DComp ((->) Env) (SComp (Writer [String]) Error) a
           -- M = (Env->) . Writer [String] . Maybe

lookup              :: Name -> Env -> Error Value
lookup x ((n,v):env) = if x==n then Ok v else lookup x env
lookup x []          = Error ("unbound variable " ++ x)

inError  :: Error a -> M a
inError   = right . right

inReader :: (Env -> a) -> M a
inReader  = left

inWriter :: Writer [String] a -> M a
inWriter  = right  . left

eval            :: Expr -> M Value
eval (Const v)   = unit v
eval (Var n)     = inReader (lookup n)                     `bind` \r  ->
                   inError r                               `bind` \x  ->
                   unit x
eval (e:+:f)     = eval e                                  `bind` \x  ->
                   eval f                                  `bind` \y  ->
                   unit (x+y)
eval (Trace m e) = eval e                                  `bind` \r  ->
                   inWriter (write [m ++ " = " ++ show r]) `bind` \() ->
                   unit r

result      :: Text a => M a -> Env -> String
result m env = unlines (["Output:"] ++ s ++ ["Result: " ++ val])
 where Result s x = open (open m env)
       val        = case x of
                      Ok x      -> show x
                      Error msg -> msg


testExpr = Trace "sum" (Const 1 :+: Const 2) :+: Var "x"

-- State monad ---------------------------------------------------------------

data State s a = ST (s -> (s,a))

instance Functor (State s) where
    fun f (ST st) = ST (\s -> let (s',x) = st s in (s',f x))

instance Premonad (State s) where
    unit x = ST (\s -> (s,x))

instance Monad (State s) where
    join (ST m) = ST (\s -> let (s', ST m') = m s
                            in  m' s')

data STM m s a = STM (s -> m (s,a))

instance Monad m => Functor (STM m s) where
    fun f (STM xs) = STM (\s -> xs s  `bind` \(s',x) -> unit (s', f x))
                -- = STM (\s -> [ (s', f x) | (s',x) <- xs s ])

instance Monad m => Premonad (STM m s) where
    unit x = STM (\s -> unit (s,x))

instance Monad m => Monad (STM m s) where
    join (STM xss) = STM (\s -> xss s `bind` \(s', STM xs) ->
                                xs s' `bind` \(s'',x)      ->
                                unit (s'',x))

                -- = STM (\s -> [ (s'',x) | (s', STM xs) <- xss s,
                --                          (s'',x) <- xs s' ])

------------------------------------------------------------------------------
