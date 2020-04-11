G52AFP Coursework 2 - Monadic Compiler

Jizhou Che
scyjc1@nottingham.ac.uk

--------------------------------------------------------------------------------

Library imports.

> import Control.Monad.Trans.Class
> import Control.Monad.Trans.Writer

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


This function compiles a single expression.

> compexpr :: Expr -> WriterT Code ST ()
> compexpr (Val i) = tell [PUSH i]
> compexpr (Var n) = tell [PUSHV n]
> compexpr (App op e1 e2) = do
>   compexpr e1
>   compexpr e2
>   tell [DO op]


This function compiles a program while maintaining the label.

> compprog :: Prog -> WriterT Code ST ()
> compprog (Assign n e) = do
>   compexpr e
>   tell [POP n]
> compprog (If e p1 p2) = do
>   l <- lift $ S (\n -> (n, n + 2))
>   compexpr e
>   tell [JUMPZ l]
>   compprog p1
>   tell [JUMP (l + 1), LABEL l]
>   compprog p2
>   tell [LABEL (l + 1)]
> compprog (While e p) = do
>   l <- lift $ S (\n -> (n, n + 2))
>   tell [LABEL l]
>   compexpr e
>   tell [JUMPZ (l + 1)]
>   compprog p
>   tell [JUMP l, LABEL (l + 1)]
> compprog (Seqn []) = tell []
> compprog (Seqn (p : ps)) = do
>   compprog p
>   compprog (Seqn ps)


This function gets the compiled code of a program.

> comp :: Prog -> Code
> comp p = fst $ app (execWriterT (compprog p)) 0


A version of the compiler without the writer monad transformer is commented below.
This is kept solely for reference, and for some pity marks if I messed up.

% > compexpr :: Expr -> Code
% > compexpr (Val i) = [PUSH i]
% > compexpr (Var n) = [PUSHV n]
% > compexpr (App op e1 e2) = compexpr e1 ++ compexpr e2 ++ [DO op]

% > compprog :: Prog -> ST Code
% > compprog (Assign n e) = return (compexpr e ++ [POP n])
% > compprog (If e p1 p2) = do
% >   c1 <- compprog p1
% >   c2 <- compprog p2
% >   l <- S (\n -> (n, n + 2))
% >   return (compexpr e ++ [JUMPZ l] ++ c1 ++ [JUMP (l + 1), LABEL l] ++ c2 ++ [LABEL (l + 1)])
% > compprog (While e p) = do
% >   c <- compprog p
% >   l <- S (\n -> (n, n + 2))
% >   return ([LABEL l] ++ compexpr e ++ [JUMPZ (l + 1)] ++ c ++ [JUMP l, LABEL (l + 1)])
% > compprog (Seqn []) = return []
% > compprog (Seqn (p : ps)) = do
% >   c <- compprog p
% >   cs <- compprog (Seqn ps)
% >   return (c ++ cs)

% > comp :: Prog -> Code
% > comp p = fst $ app (compprog p) 0

--------------------------------------------------------------------------------

Simulator.


This function sets the value of a variable in the memory.

> memset :: Mem -> (Name, Int) -> Mem
> memset [] ni = [ni]
> memset (ni : nis) (n, i) | fst ni == n = (n, i) : nis
>                          | otherwise = ni : memset nis (n, i)


This function gets the value of a variable in the memory.

> memget :: Mem -> Name -> Int
> memget (ni : nis) n | fst ni == n = snd ni
>                     | otherwise = memget nis n


This function executes a single instruction.
The resulting stack and memory are returned as the first two elements of the tuple.
The third element of the tuple marks the integer label to jump to, or is set to -1 if no jumping is required.

> execinst :: Inst -> Stack -> Mem -> (Stack, Mem, Int)
> execinst (PUSH i) s m = (i : s, m, -1)
> execinst (PUSHV n) s m = ((memget m n) : s, m, -1)
> execinst (POP n) s m = (tail s, memset m (n, head s), -1)
> execinst (DO op) s m | op == Add = (s !! 1 + s !! 0 : drop 2 s, m, -1)
>                      | op == Sub = (s !! 1 - s !! 0 : drop 2 s, m, -1)
>                      | op == Mul = (s !! 1 * s !! 0 : drop 2 s, m, -1)
>                      | op == Div = (s !! 1 `div` s !! 0 : drop 2 s, m, -1)
> execinst (JUMP l) s m = (s, m, l)
> execinst (JUMPZ l) s m | head s == 0 = (tail s, m, l)
>                        | otherwise = (tail s, m, -1)
> execinst (LABEL l) s m = (s, m, -1)


This function executes the code while maintaining the stack, the memory, and jumping.
The code is split into two parts: the executed instructions, and the remaining instructions.
Jumping to a label will simply resplit the code.

> execcode :: (Code, Code) -> (Stack, Mem, Int) -> (Stack, Mem, Int)
> execcode (_, []) mt = mt
> execcode (c1, c2) (s, m, l) | l < 0 = execcode (c1 ++ [head c2], tail c2) $ execinst (head c2) s m
>                             | otherwise = execcode cp (s, m, -1)
>                                           where cp = break (\inst -> inst == (LABEL l)) (c1 ++ c2)


This function gets the resulting memory of executing a piece of code.

> exec :: Code -> Mem
> exec c = (\(_, m, _) -> m) (execcode ([], c) ([], [], -1))
