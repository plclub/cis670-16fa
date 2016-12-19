-- | Old compilers, will not compile with newer language changes.

-- =======================================================================================
-- | First compiler turns everything into a dynamic type. Uses a lot of unnecessary
-- | casting to work though.
compileDyn :: DL.Exp -> StaticExp Dynamic
compileDyn (DL.Lam str exp)       =
  To $ Lam str (compileDyn exp)

-- No need to To we already return a Dynamic after function application.
compileDyn (f DL.:@ exp)          =
  From (compileDyn f) :@ (compileDyn exp)

compileDyn (DL.Bin op exp1 exp2)  =
  To $ IntBin op sExp1 sExp2
  where sExp1 = From $ compileDyn exp1
        sExp2 = From $ compileDyn exp2

compileDyn (DL.Lit n)             = To (IntLit n)
compileDyn (DL.Var str)           = Var str

-- the "compileDyn exps" are both of type Dynamic so the entire expression has
-- type Dynamic.
compileDyn (DL.If cond exp1 exp2) =
  If (compileDyn cond) (compileDyn exp1) (compileDyn exp2)
-- =======================================================================================

data Result where
  Result :: (Typeable t) => StaticExp t -> Result

printResults :: Result -> IO()
printResults (Result exp) = putStrLn (show exp)

-- | The issue with `compileDyn` is the return type of all cases must be the same
-- | StaticExp t, so t must be Dynamic. Instead we wrap the results in type.
compileRes :: DL.Exp -> Result
-- The second argument of a Lam must be dynamic.
compileRes (DL.Lam str exp)       = case (compileRes exp) of
  Result exp' -> Result $ Lam str (ensureDyn exp')

compileRes (f DL.:@ exp)          =
  case (compileRes f, compileRes exp) of
    (Result f', Result exp') ->
      Result (castType f' :@ (ensureDyn exp') :: StaticExp Dynamic)

compileRes (DL.Bin op exp1 exp2)  =
  case (compileRes exp1, compileRes exp2) of
    -- Bin requires the type of both operators to be the same and that's the
    -- type of the whole expression. After compileRes there is no guarantee the
    -- types are the same so we must explicitly cast them if they are the same.
    (Result exp1', Result exp2') -> Result $ Bin op (castType exp1') (castType exp2')

compileRes (DL.Lit n)             = Result (Lit n)
compileRes (DL.Var str)           = Result (Var str)

compileRes (DL.If cond exp1 exp2) =
  case (compileRes cond, compileRes exp1, compileRes exp2) of
    -- We expect the type of both branches of an If to be the same, else it may not
    -- necessarly be wrong as one branch may return a dynamic. So we wrap both sides
    -- in dynamics.
    (Result cond',
     -- Get the type of both expressions to compare.
     Result (exp1' :: StaticExp a),
     Result (exp2' :: StaticExp b)) ->
      case eqT (typeRep :: TypeRep a) (typeRep :: TypeRep b) of
      Just Refl -> Result $ If (ensureDyn cond') exp1' exp2'
      Nothing   -> Result $ If (ensureDyn cond') (ensureDyn exp1') (ensureDyn exp2')


-- We want to cast from an 'a' to a 'b' but our types are wrapped in a
-- StaticExp so we use gcast!
-- gcast :: forall a b c. (Typeable a, Typeable b) => c a -> Maybe (c b)

-- | Given an StaticExp t1 we attempt to cast to a t2 if the types are the same.
-- | If it is a Dynamic we add a call to From and defer this check to run time.
-- | Otherwise we for sure have an error.
castType :: (Typeable t1, Typeable t2) => StaticExp t1 -> StaticExp t2
castType t = case gcast t of
            Just i -> i
            Nothing -> case gcast t of
              Just i -> From i
              Nothing -> error $ "castType: They type of " ++ show t ++
                " does not match t2 or Dynamic."

-- | Given a typeable value check if it's Dynamic, else we add turn in into a Dynamic
-- | by wrapping it in a To.
ensureDyn :: forall t. Typeable t => StaticExp t -> StaticExp Dynamic
ensureDyn val = case (eqT (typeRep :: TypeRep t) (typeRep :: TypeRep Dynamic)) of
  Just Refl  -> val
  Nothing    -> To val

testCompileRes :: DL.Exp -> StaticExp Int
testCompileRes e = case compileRes e of
  (Result e') -> castType e'
-- =======================================================================================
