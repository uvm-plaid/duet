module Duet.Parser where

import UVMHS

import Duet.Syntax
import Duet.RExp
import Duet.Quantity
import Duet.Var

data Token =
    TokenName 𝕊
  | TokenLiteral 𝕊
  | TokenInteger ℤ
  | TokenDouble 𝔻
  | TokenComment
  | TokenSpace
  deriving (Eq,Ord,Show)
makePrisms ''Token
makePrettyUnion ''Token

tokKeywords ∷ 𝐿 𝕊
tokKeywords = list
  ["let","in","pλ","return","on"
  ,"ℕ","ℝ","ℝ⁺","𝔻","𝕀","𝕄"
  ,"LR","L2","U"
  ,"real"
  ,"matrix","mcreate","clip","∇","mmap","idx"
  ,"aloop","loop","mgauss","rows","cols","exponential","rand-resp"
  ,"sample","rand-nat"
  ,"L1","L2","L∞","U"
  ,"dyn","real"
  ]

tokPunctuation ∷ 𝐿 𝕊
tokPunctuation = list
  ["=",":","@",".","⇒","→","←","#","↦"
  ,"[","]","(",")","{","}","<",">",",",";","|","⟨","⟩"
  ,"⊔","⊓","+","⋅","/","√","㏒"
  ,"-","%","≟"
  ,"×","&","⊸","⊸⋆"
  ]

tokComment ∷ Parser ℂ ()
tokComment = pNew "comment" $ do
  void $ pWord "--"
  void $ pMany $ pSatisfies "not newline" $ \ c → c ≢ '\n'
  void $ pLit '\n'

tokMLComment ∷ Parser ℂ ()
tokMLComment = pNew "multiline comment" $ do
  () ← void $ pWord "{-"
  afterOther
  where
    afterOther = tries
      [ do () ← void $ pSatisfies "non-delimiter" $ \ c → c ∉ pow ['{','-'] 
           afterOther
      , do () ← void $ pLit '{' 
           afterBrack
      , do () ← void $ pLit '-' 
           afterDash
      ]
    afterBrack = tries
      [ do () ← void $ pSatisfies "non-delimiter" $ \ c → c ∉ pow ['{','-']
           afterOther
      , do () ← void $ pLit '{' 
           afterBrack
      , do () ← void $ pLit '-' 
           () ← afterOther
           afterOther
      ]
    afterDash = tries
      [ do () ← void $ pSatisfies "non-delimiter" $ \ c → c ∉ pow ['{','-','}']
           afterOther
      , do () ← void $ pLit '{'
           afterBrack
      , do () ← void $ pLit '-'
           afterDash
      , do void $ pLit '}'
      ]

tokDuet ∷ 𝐿 (Parser ℂ Token)
tokDuet = list $ concat
  [ TokenLiteral ^∘ pRender (FG darkYellow) ∘ pRender BD ∘ pWord ^$ tokKeywords
  , TokenLiteral ^∘ pRender (FG darkGray) ∘ pWord ^$ tokPunctuation
  , single $ TokenName ^$ pRender (FG black) pName
  , single $ map (elimChoice TokenInteger TokenDouble) $ pRender (FG darkRed) pNumber
  , map (const TokenComment) ∘ pRender (FG gray) ∘ pRender IT ^$ list [tokComment,tokMLComment]
  , single $ const TokenSpace ^$ pWhitespace
  ]

parLit ∷ 𝕊 → Parser Token ()
parLit = void ∘ pLit ∘ TokenLiteral

parVar ∷ Parser Token 𝕏
parVar = var ^$ pShaped "name" $ view tokenNameL

parInt ∷ Parser Token ℤ
parInt = pShaped "int" $ view tokenIntegerL

parNat ∷ Parser Token ℕ
parNat = pShaped "nat" $ \ t → do
  i ← view tokenIntegerL t
  natO i

parDbl ∷ Parser Token 𝔻
parDbl = pShaped "dbl" $ view tokenDoubleL

parNNDbl ∷ Parser Token 𝔻
parNNDbl = pShaped "nn-dbl" $ \ t → do
  d ← view tokenDoubleL t
  case d ≥ 0.0 of
    True → return d
    False → abort

parKind ∷ Parser Token Kind
parKind = pNew "kind" $ tries
  [ do parLit "ℕ" ; return ℕK
  , do parLit "ℝ⁺" ; return ℝK
  ]

parRExp ∷ Parser Token RExp
parRExp = mixfixParserWithContext "rexp" $ concat
  [ mixF $ MixFTerminal $ VarRE ^$ parVar
  , mixF $ MixFTerminal $ NatRE ^$ parNat
  , mixF $ MixFTerminal $ NNRealRE ^$ parNNDbl
  , mixF $ MixFInfixL 2 $ const MaxRE ^$ parLit "⊔"
  , mixF $ MixFInfixL 3 $ const MinRE ^$ parLit "⊓"
  , mixF $ MixFInfixL 4 $ const PlusRE ^$ parLit "+"
  , mixF $ MixFInfixL 5 $ const TimesRE ^$ parLit "⋅"
  , mixF $ MixFInfixL 6 $ const DivRE ^$ parLit "/"
  , mixF $ MixFPrefix 7 $ const RootRE ^$ parLit "√"
  , mixF $ MixFPrefix 7 $ const LogRE ^$ parLit "㏒"
  ]

parNorm ∷ Parser Token Norm
parNorm = tries
  [ do const L1 ^$ parLit "L1"
  , do const L2 ^$ parLit "L2"
  , do const LInf ^$ parLit "L∞"
  ]

parClip ∷ Parser Token Clip
parClip = tries
  [ do NormClip ^$ parNorm
  , do const UClip ^$ parLit "U"
  ]

parSens ∷ Parser Token (Sens RExp)
parSens = Sens ∘ Quantity ^$ parRExp

parPriv ∷ Parser Token (Priv p RExp)
parPriv = undefined

parSpace ∷ Parser Token ()
parSpace = pSkip (const False) $ void $ pOneOrMore $ tries
  [ pLit TokenComment
  , pLit TokenSpace
  ]

parTypeSource ∷ Parser Token (TypeSource p RExp)
parTypeSource = pWithContext "type" parType

parType ∷ Parser Token (Type p RExp)
parType = mixfixParser $ concat
  [ mix $ MixTerminal $ do
      parLit "ℕ"
      parLit "["
      η ← parRExp
      parLit "]"
      return $ ℕˢT η
  , mix $ MixTerminal $ do
      parLit "ℝ⁺"
      parLit "["
      η ← parRExp
      parLit "]"
      return $ ℝˢT η
  , mix $ MixTerminal $ const ℕT ^$ parLit "ℕ"
  , mix $ MixTerminal $ const ℝT ^$ parLit "ℝ"
  , mix $ MixTerminal $ const 𝔻T ^$ parLit "𝔻"
  , mix $ MixTerminal $ do
      parLit "𝕀"
      parLit "["
      η ← parRExp
      parLit "]"
      return $ 𝕀T η
  , mix $ MixPrefix 10 $ do
      parLit "𝕄"
      parLit "["
      ℓ ← parNorm
      c ← parClip
      parLit "|"
      ηₘ ← parRExp
      parLit ","
      ηₙ ← parRExp
      parLit "]"
      return $ 𝕄T ℓ c ηₘ ηₙ
  , mix $ MixInfixL 3 $ const (:+:) ^$ parLit "+"
  , mix $ MixInfixL 4 $ const (:×:) ^$ parLit "×"
  , mix $ MixInfixL 4 $ const (:&:) ^$ parLit "&"
  , mix $ MixInfixR 2 $ do
      parLit "⊸"
      parLit "["
      s ← parSens
      parLit "]"
      return $ \ τ₁ τ₂ → τ₁ :⊸: (s :* τ₂)
  , mix $ MixPrefix 2 $ do
      parLit "∀"
      ακs ← pOneOrMoreSepBy (parLit ",") $ do
        α ← parVar
        parLit ":"
        κ ← parKind
        return $ α :* κ
      parLit "."
      τps ← pOneOrMoreSepBy (parLit ",") $ do
        τ ← parType
        parLit "@"
        p ← parPriv
        return $ τ :* p
      return $ (:⊸⋆:) $ ακs :* τps
  ]

parGrad ∷ Parser Token Grad
parGrad = tries
  [ const LR ^$ parLit "LR"
  ]

parSExp ∷ PRIV_W p → Parser Token (SExpSource p)
parSExp p = mixfixParserWithContext "sexp" $ concat
  [ mixF $ MixFTerminal $ do
      parLit "("
      e ← parSExp p
      parLit ")"
      return $ extract e
  , mixF $ MixFTerminal $ do
      parLit "ℕ"
      parLit "["
      n ← parNat
      parLit "]"
      return $ ℕˢSE n
  , mixF $ MixFTerminal $ do
      parLit "ℝ⁺"
      parLit "["
      d ← parNNDbl
      parLit "]"
      return $ ℝˢSE d
  , mixF $ MixFPrefix 10 $ const DynSE ^$ parLit "dyn"
  , mixF $ MixFTerminal $ ℕSE ^$ parNat
  , mixF $ MixFTerminal $ ℝSE ^$ parDbl
  , mixF $ MixFPrefix 10 $ const RealSE ^$ parLit "real"
  , mixF $ MixFInfixL 3 $ const MaxSE ^$ parLit "⊔"
  , mixF $ MixFInfixL 4 $ const MinSE ^$ parLit "⊓"
  , mixF $ MixFInfixL 5 $ const PlusSE ^$ parLit "+"
  , mixF $ MixFInfixL 6 $ const TimesSE ^$ parLit "⋅"
  , mixF $ MixFInfixL 7 $ const DivSE ^$ parLit "/"
  , mixF $ MixFPrefix 8 $ const RootSE ^$ parLit "√"
  , mixF $ MixFPrefix 8 $ const LogSE ^$ parLit "㏒"
  , mixF $ MixFInfixL 7 $ const ModSE ^$ parLit "%"
  , mixF $ MixFInfixL 5 $ const MinusSE ^$ parLit "-"
  , mixF $ MixFInfixL 2 $ const MinusSE ^$ parLit "≟"
  , mixF $ MixFTerminal $ do
      parLit "mcreate"
      parLit "["
      ℓ ← parNorm
      parLit "|"
      e₁ ← parSExp p
      parLit ","
      e₂ ← parSExp p
      parLit "]"
      parLit "{"
      x₁ ← parVar
      parLit ","
      x₂ ← parVar
      parLit "⇒"
      e₃ ← parSExp p
      parLit "}"
      return $ MCreateSE ℓ e₁ e₂ x₁ x₂ e₃
  , mixF $ MixFPostfix 10 $ do
      parLit "#"
      parLit "["
      e₂ ← parSExp p
      parLit ","
      e₃ ← parSExp p
      e₄O ← pOptional $ do
        parLit "↦"
        parSExp p
      parLit "]"
      return $ case e₄O of
        None → \ e₁ → MIndexSE e₁ e₂ e₃
        Some e₄ → \ e₁ → MUpdateSE e₁ e₂ e₃ e₄
  , mixF $ MixFPrefix 10 $ const MRowsSE ^$ parLit "rows"
  , mixF $ MixFPrefix 10 $ const MColsSE ^$ parLit "cols"
  , mixF $ MixFPrefix 10 $ const IdxSE ^$ parLit "idx"
  , mixF $ MixFPrefix 10 $ do
      parLit "clip"
      parLit "["
      ℓ ← parNorm
      parLit "]"
      return $ MClipSE ℓ
  , mixF $ MixFTerminal $ do
      parLit "∇"
      parLit "["
      g ← parGrad
      parLit "|"
      e₁ ← parSExp p
      parLit ";"
      e₂ ← parSExp p
      parLit ","
      e₃ ← parSExp p
      parLit "]"
      return $ MLipGradSE g e₁ e₂ e₃
  , mixF $ MixFTerminal $ do
      parLit "mmap"
      e₁ ← parSExp p
      e₂O ← pOptional $ do
        parLit ","
        e₂ ← parSExp p
        return e₂
      parLit "{"
      x₁ ← parVar
      e₂x₂O ← case e₂O of
        None → return None
        Some e₂ → do
          parLit ","
          x₂ ← parVar
          return $ Some $ e₂ :* x₂
      parLit "⇒"
      e₃ ← parSExp p
      parLit "}"
      return $ case e₂x₂O of
        None → MMapSE e₁ x₁ e₃
        Some (e₂ :* x₂) → MMap2SE e₁ e₂ x₁ x₂ e₃
  , mixF $ MixFTerminal $ VarSE ^$ parVar
  , mixF $ MixFPrefix 1 $ do
      parLit "let"
      tries
        [ do x ← parVar
             parLit "="
             e₁ ← parSExp p
             parLit "in"
             return $ \ e₂ → LetSE x e₁ e₂
        , do parLit "⟨"
             x ← parVar
             parLit ","
             y ← parVar
             parLit "⟩"
             parLit "="
             e₁ ← parSExp p
             parLit "in"
             return $ \ e₂ → UntupSE x y e₁ e₂
        ]
  , mixF $ MixFInfixL 10 $ const AppSE ^$ parSpace
  , mixF $ MixFTerminal $ do
      parLit "pλ"
      ακs ← pOneOrMoreSepBy (parLit ",") $ do
        α ← parVar
        parLit ":"
        κ ← parKind
        return $ α :* κ
      parLit "."
      xτs ← pOneOrMoreSepBy (parLit ",") $ do
        x ← parVar
        parLit ":"
        τ ← parTypeSource
        return $ x :* τ
      parLit "⇒"
      e ← parPExp p
      return $ PFunSE ακs xτs e
  , mixF $ MixFTerminal $ do 
       parLit "⟨"
       e₁ ← parSExp p
       parLit ","
       e₂ ← parSExp p
       parLit "⟩"
       return $ TupSE e₁ e₂
  ]

parPExp ∷ PRIV_W p → Parser Token (PExpSource p)
parPExp p = pWithContext "pexp" $ tries
  [ do parLit "let"
       x ← parVar
       parLit "="
       e₁ ← parSExp p
       parLit "in"
       e₂ ← parPExp p
       return $ BindPE x (ReturnPE %⋅ e₁) e₂
  , do parLit "return"
       e ← parSExp p
       return $ ReturnPE e
  , do x ← parVar
       parLit "←"
       e₁ ← parPExp p
       parLit ";"
       e₂ ← parPExp p
       return $ BindPE x e₁ e₂
  , case p of
      ED_W → do 
        parLit "aloop"
        parLit "["
        e₁ ← parSExp p
        parLit "]"
        e₂ ← parSExp p
        parLit "on"
        e₃ ← parSExp p
        parLit "<"
        xs ← pManySepBy (parLit ",") parVar
        parLit ">"
        parLit "{"
        x₁ ← parVar
        parLit ","
        x₂ ← parVar
        parLit "⇒"
        e₄ ← parPExp p
        parLit "}"
        return $ EDLoopPE e₁ e₂ e₃ xs x₁ x₂ e₄
      ZC_W → do 
        parLit "loop"
        e₂ ← parSExp p
        parLit "on"
        e₃ ← parSExp p
        parLit "<"
        xs ← pManySepBy (parLit ",") parVar
        parLit ">"
        parLit "{"
        x₁ ← parVar
        parLit ","
        x₂ ← parVar
        parLit "⇒"
        e₄ ← parPExp p
        parLit "}"
        return $ LoopPE e₂ e₃ xs x₁ x₂ e₄
      _ → abort
  , case p of
      ED_W → do 
        parLit "mgauss"
        parLit "["
        e₁ ← parSExp p
        parLit ","
        e₂ ← parSExp p
        parLit ","
        e₃ ← parSExp p
        parLit "]"
        parLit "<"
        xs ← pManySepBy (parLit ",") parVar
        parLit ">"
        parLit "{"
        e₄ ← parSExp p
        parLit "}"
        return $ MGaussPE e₁ (EDGaussParams e₂ e₃) xs e₄
      ZC_W → do 
        parLit "mgauss"
        parLit "["
        e₁ ← parSExp p
        parLit ","
        e₂ ← parSExp p
        parLit "]"
        parLit "<"
        xs ← pManySepBy (parLit ",") parVar
        parLit ">"
        parLit "{"
        e₄ ← parSExp p
        parLit "}"
        return $ MGaussPE e₁ (ZCGaussParams e₂) xs e₄
      _ → abort
  , case p of
      ED_W → do 
        parLit "exponential"
        parLit "["
        e₁ ← parSExp p
        parLit ","
        e₂ ← parSExp p
        parLit "]"
        e₃ ← parSExp p
        parLit "<"
        xs ← pManySepBy (parLit ",") parVar
        parLit ">"
        parLit "{"
        x ← parVar
        parLit "⇒"
        e₄ ← parSExp p
        parLit "}"
        return $ ExponentialPE e₁ (EDExponentialParams e₂) e₃ xs x e₄
      _ → abort
  , case p of
      ED_W → do
        parLit "rand-resp"
        parLit "["
        e₁ ← parSExp p
        parLit ","
        e₂ ← parSExp p
        parLit "]"
        parLit "<"
        xs ← pManySepBy (parLit ",") parVar
        parLit ">"
        parLit "{"
        e₃ ← parSExp p
        parLit "}"
        return $ RRespPE e₁ e₂ xs e₃
      _ → abort
  , case p of
      ED_W → do
        parLit "sample"
        parLit "["
        e₁ ← parSExp p
        parLit "]"
        e₂ ← parSExp p
        parLit ","
        e₃ ← parSExp p
        parLit "{"
        x₁ ← parVar
        parLit ","
        x₂ ← parVar
        parLit "⇒"
        e₄ ← parPExp p
        parLit "}"
        return $ SamplePE e₁ e₂ e₃ x₁ x₂ e₄
      _ → abort
  , do parLit "rand-nat"
       parLit "["
       e₁ ← parSExp p
       parLit ","
       e₂ ← parSExp p
       parLit "]"
       return $ RandNatPE e₁ e₂
  ]

tokSkip ∷ Token → 𝔹
tokSkip = \case
  TokenSpace → True
  TokenComment → True
  _ → False

  -- [ mix $ MixTerminal $ do
  --     void $ pSatisfies "lparen" $ shape eTLParenL
  --     x ← parseExp
  --     void $ pSatisfies "rparen" $ shape eTRParenL
  --     return x
  -- , mix $ MixTerminal  $ EAtom ∘ ASymbol ^$ pShaped "symbol" $ view eTSymbolL
  -- , mix $ MixTerminal  $ EAtom ∘ ANatural ^$ pShaped "natural" $ view eTNaturalL
  -- , mix $ MixInfixR  5 $ const ESum ^$ surroundWhitespace $ pShaped "plus" $ view eTPlusL
  -- , mix $ MixInfixR  6 $ const EProduct ^$ surroundWhitespace $ pShaped "times" $ view eTTimesL
  -- , mix $ MixInfixL  7 $ const EExpo ^$ surroundWhitespace $ pShaped "power" $ view eTPowerL
  -- , mix $ MixPostfix 7 $ const EFact ^$ preWhitespace $ pShaped "fact" $ view eTFactL
  -- , mix $ MixPrefix  8 $ const ENegate ^$ postWhitespace $ pShaped "neg" $ view eTNegativeL
  -- , mix $ MixInfix   5 $ const EEquality ^$ surroundWhitespace $ pShaped "equal" $ view eTEqualL
  -- ]
  -- where
  --   surroundWhitespace ∷ Parser ExpToken a → Parser ExpToken a
  --   surroundWhitespace xM = do
  --     void $ pOptional $ pSatisfies "whitespace" $ shape eTWhitespaceL
  --     x ← xM
  --     void $ pOptional $ pSatisfies "whitespace" $ shape eTWhitespaceL
  --     return x
  --   preWhitespace ∷ Parser ExpToken a → Parser ExpToken a
  --   preWhitespace xM = do
  --     void $ pOptional $ pSatisfies "whitespace" $ shape eTWhitespaceL
  --     xM
  --   postWhitespace ∷ Parser ExpToken a → Parser ExpToken a
  --   postWhitespace xM = do
  --     x ← xM
  --     void $ pOptional $ pSatisfies "whitespace" $ shape eTWhitespaceL
  --     return x
