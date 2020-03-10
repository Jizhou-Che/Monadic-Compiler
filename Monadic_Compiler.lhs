G52AFP Coursework 2 - Monadic Compiler

Jizhou Che
scyjc1@nottingham.ac.uk

--------------------------------------------------------------------------------

Imperative language:

> data Prog = Assign Name Expr
>           | If Expr Prog Prog
>           | While Expr Prog
>           | Seqn [Prog]
>             deriving Show
>
> data Expr = Val Int | Var Name | App Op Expr Expr
>             deriving Show
>
> type Name = Char
>
> data Op   = Add | Sub | Mul | Div
>             deriving (Show, Eq)

Factorial example:

> fac :: Int -> Prog
> fac n = Seqn [Assign 'A' (Val 1),
>               Assign 'B' (Val n),
>               While (Var 'B') (Seqn
>                  [Assign 'A' (App Mul (Var 'A') (Var 'B')),
>                   Assign 'B' (App Sub (Var 'B') (Val (1)))])]

Virtual machine:

> type Stack = [Int]
>
> type Mem   = [(Name,Int)]
>
> type Code  = [Inst]
> 
> data Inst  = PUSH Int
>            | PUSHV Name
>            | POP Name
>            | DO Op
>            | JUMP Label
>            | JUMPZ Label
>            | LABEL Label
>              deriving (Show, Eq)
> 
> type Label = Int

State monad:

> type State = Label
>
> newtype ST a = S (State -> (a, State))
>
> app :: ST a -> State -> (a,State)
> app (S st) x 	=  st x
>
> instance Functor ST where
>    -- fmap :: (a -> b) -> ST a -> ST b
>    fmap g st = S (\s -> let (x,s') = app st s in (g x, s'))
>
> instance Applicative ST where
>    -- pure :: a -> ST a
>    pure x = S (\s -> (x,s))
>
>    -- (<*>) :: ST (a -> b) -> ST a -> ST b
>    stf <*> stx = S (\s ->
>       let (f,s')  = app stf s
>           (x,s'') = app stx s' in (f x, s''))
>
> instance Monad ST where
>    -- return :: a -> ST a
>    return x = S (\s -> (x,s))
>
>    -- (>>=) :: ST a -> (a -> ST b) -> ST b
>    st >>= f = S (\s -> let (x,s') = app st s in app (f x) s')

--------------------------------------------------------------------------------

Compiler.

> compexpr :: Expr -> Code
> compexpr (Val i) = [PUSH i]
> compexpr (Var n) = [PUSHV n]
> compexpr (App op e1 e2) = compexpr e1 ++ compexpr e2 ++ [DO op]

> compprog :: Prog -> Label -> (Code, Label)
> compprog (Assign n e) l = (compexpr e ++ [POP n], l)
> compprog (If e p1 p2) l = (compexpr e ++ [JUMPZ l''] ++ c1 ++ [JUMP (l'' + 1), LABEL l''] ++ c2 ++ [LABEL (l'' + 1)], l'' + 2)
>                           where (c1, l') = compprog p1 l
>                                 (c2, l'') = compprog p2 l'
> compprog (While e p) l = ([LABEL l'] ++ compexpr e ++ [JUMPZ (l' + 1)] ++ c ++ [JUMP l', LABEL (l' + 1)], l' + 2)
>                          where (c, l') = compprog p l
> compprog seqn l = (concat (map fst cls), snd (last cls))
>                   where cls = compseqn seqn l

> compseqn :: Prog -> Label -> [(Code, Label)]
> compseqn (Seqn []) l = [([], l)]
> compseqn (Seqn (p : ps)) l = (c, l') : compseqn (Seqn ps) l'
>                              where (c, l') = compprog p l

> comp :: Prog -> Code
> comp p = fst $ compprog p 0

--------------------------------------------------------------------------------

Simulator.

This function is foldable.

> memset :: Mem -> (Name, Int) -> Mem
> memset [] ni = [ni]
> memset (ni : nis) (n, i) | fst ni == n = (n, i) : nis
>                          | otherwise = ni : memset nis (n, i)

This function is foldable.

> memget :: Mem -> Name -> Maybe Int
> memget [] _ = Nothing
> memget (ni : nis) n | fst ni == n = Just $ snd ni
>                     | otherwise = memget nis n

> execinst :: Inst -> Stack -> Mem -> Maybe (Stack, Mem, Int)
> execinst (PUSH i) s m = Just (i : s, m, -1)
> execinst (PUSHV n) s m | memget m n == Nothing = Nothing
>                        | otherwise = Just (v : s, m, -1)
>                                      where Just v = memget m n
> execinst (POP n) s m | s == [] = Nothing
>                      | otherwise = Just (tail s, memset m (n, head s), -1)
> execinst (DO op) s m | length s < 2 = Nothing
>                      | op == Add = Just (s !! 1 + s !! 0 : drop 2 s, m, -1)
>                      | op == Sub = Just (s !! 1 - s !! 0 : drop 2 s, m, -1)
>                      | op == Mul = Just (s !! 1 * s !! 0 : drop 2 s, m, -1)
>                      | op == Div && head s /= 0 = Just (s !! 1 `div` s !! 0 : drop 2 s, m, -1)
>                      | otherwise = Nothing
> execinst (JUMP l) s m = Just (s, m, l)
> execinst (JUMPZ l) s m | s == [] = Nothing
>                        | head s == 0 = Just (tail s, m, l)
>                        | otherwise = Just (tail s, m, -1)
> execinst (LABEL l) s m = Just (s, m, -1)

> execcode :: (Code, Code) -> Maybe (Stack, Mem, Int) -> Maybe (Stack, Mem, Int)
> execcode _ Nothing = Nothing
> execcode (_, []) mt = mt
> execcode (c1, c2) (Just (s, m, l)) | l < 0 = execcode (c1 ++ [head c2], tail c2) $ execinst (head c2) s m
>                                    | otherwise = execcode cp (Just (s, m, -1))
>                                                  where cp = break (\inst -> inst == (LABEL l)) (c1 ++ c2)

> exec :: Code -> Maybe Mem
> exec c | execcode ([], c) (Just ([], [], -1)) == Nothing = Nothing
>        | otherwise = Just $ (\(_, m, _) -> m) t
>          where Just t = execcode ([], c) (Just ([], [], -1))
