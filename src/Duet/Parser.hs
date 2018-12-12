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
  ,"matrix","mcreate","clip","L∇","U∇"
  ,"loop","mgauss","rows","cols"
  ,"L1","L2","L∞","U"
  ,"dyn","real"
  ]

tokPunctuation ∷ 𝐿 𝕊
tokPunctuation = list
  ["=",":","@",".","⇒","→","←"
  ,"[","]","(",")","{","}","<",">",",",";","|"
  ,"⊔","⊓","+","⋅","/","√","log"
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

parName ∷ Parser Token 𝕊
parName = pShaped "name" $ view tokenNameL

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
parKind = pWithContext "kind" $ tries
  [ do parLit "ℕ" ; return ℕK
  , do parLit "ℝ⁺" ; return ℝK
  ]

parRExp ∷ Parser Token RExp
parRExp = mixfixParserWithContext "rexp" $ concat
  [ mixF $ MixFTerminal $ VarRE ∘ var ^$ parName
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

parPriv ∷ Parser Token (Priv ID RExp)
parPriv = Priv ∘ Quantity ∘ ID ^$ parRExp

parSpace ∷ Parser Token ()
parSpace = pSkip (const False) $ void $ pOneOrMore $ tries
  [ pLit TokenComment
  , pLit TokenSpace
  ]

parType ∷ Parser Token (Type ID RExp)
parType = mixfixParserWithContext "type" $ concat
  [ mixF $ MixFTerminal $ do
      parLit "ℕ"
      parLit "["
      η ← parRExp
      parLit "]"
      return $ ℕˢT η
  , mixF $ MixFTerminal $ do
      parLit "ℝ⁺"
      parLit "["
      η ← parRExp
      parLit "]"
      return $ ℝˢT η
  , mixF $ MixFTerminal $ const ℕT ^$ parLit "ℕ"
  , mixF $ MixFTerminal $ const ℝT ^$ parLit "ℝ"
  , mixF $ MixFTerminal $ const 𝔻T ^$ parLit "𝔻"
  , mixF $ MixFTerminal $ do
      parLit "𝕀"
      parLit "["
      η ← parRExp
      parLit "]"
      return $ 𝕀T η
  , mixF $ MixFPrefix 10 $ do
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
  , mixF $ MixFInfixL 3 $ const (:+:) ^$ parLit "+"
  , mixF $ MixFInfixL 4 $ const (:×:) ^$ parLit "×"
  , mixF $ MixFInfixL 4 $ const (:&:) ^$ parLit "&"
  , mixF $ MixFInfixR 2 $ do
      parLit "⊸"
      parLit "["
      s ← parSens
      parLit "]"
      return $ \ τ₁ τ₂ → τ₁ :⊸: (s :* τ₂)
  , mixF $ MixFPrefix 2 $ do
      parLit "∀"
      ακs ← pOneOrMoreSepBy (parLit ",") $ do
        α ← parName
        parLit ":"
        κ ← parKind
        return $ var α :* κ
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

parSExp ∷ Parser Token (SExp ID)
parSExp = mixfixParserWithContext "sexp" $ concat
  [ mixF $ MixFTerminal $ do
      parLit "("
      e ← parSExp
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
      e₁ ← parSExp
      parLit ","
      e₂ ← parSExp
      parLit "]"
      parLit "{"
      x₁ ← parName
      parLit ","
      x₂ ← parName
      parLit "⇒"
      e₃ ← parSExp
      parLit "}"
      return $ MCreateSE ℓ e₁ e₂ (var x₁) (var x₂) e₃
  , mixF $ MixFPrefix 10 $ const MRowsSE ^$ parLit "rows"
  , mixF $ MixFPrefix 10 $ const MColsSE ^$ parLit "cols"
  , mixF $ MixFPrefix 10 $ do
      parLit "clip"
      parLit "["
      ℓ ← parNorm
      parLit "]"
      return $ MClipSE ℓ
  , mixF $ MixFTerminal $ do
      parLit "L∇"
      parLit "["
      g ← parGrad
      ℓ ← parNorm
      parLit "|"
      e₁ ← parSExp
      parLit ";"
      e₂ ← parSExp
      parLit ","
      e₃ ← parSExp
      parLit "]"
      return $ MLipGradSE g ℓ e₁ e₂ e₃
  , mixF $ MixFTerminal $ VarSE ∘ var ^$ parName
  , mixF $ MixFPrefix 1 $ do
      parLit "let"
      x ← parName
      parLit "="
      e₁ ← parSExp
      parLit "in"
      return $ \ e₂ → LetSE (var x) e₁ e₂
  , mixF $ MixFInfixL 10 $ const AppSE ^$ parSpace
  , mixF $ MixFTerminal $ do
      parLit "pλ"
      ακs ← pOneOrMoreSepBy (parLit ",") $ do
        α ← parName
        parLit ":"
        κ ← parKind
        return $ var α :* κ
      parLit "."
      xτs ← pOneOrMoreSepBy (parLit ",") $ do
        x ← parName
        parLit ":"
        τ ← parType
        return $ var x :* τ
      parLit "⇒"
      e ← parPExp
      return $ PFunSE ακs xτs e
  ]

parPExp ∷ Parser Token (PExp ID)
parPExp = pWithContext "pexp" $ tries
  [ do parLit "let"
       x ← parName
       parLit "="
       e₁ ← parSExp
       parLit "in"
       e₂ ← parPExp
       return $ BindPE (var x) (ReturnPE %⋅ e₁) e₂
  , do parLit "return"
       e ← parSExp
       return $ ReturnPE e
  , do x ← var ^$ parName
       parLit "←"
       e₁ ← parPExp
       parLit ";"
       e₂ ← parPExp
       return $ BindPE x e₁ e₂
  , do parLit "loop"
       parLit "["
       e₁ ← parSExp
       parLit "]"
       e₂ ← parSExp
       parLit "on"
       e₃ ← parSExp
       parLit "<"
       xs ← var ^^$ pManySepBy (parLit ",") parName
       parLit ">"
       parLit "{"
       x₁ ← var ^$ parName
       parLit ","
       x₂ ← var ^$ parName
       parLit "⇒"
       e₄ ← parPExp
       parLit "}"
       return $ LoopPE e₁ e₂ e₃ xs x₁ x₂ e₄
  , do parLit "mgauss"
       parLit "["
       e₁ ← parSExp
       parLit ","
       e₂ ← parSExp
       parLit ","
       e₃ ← parSExp
       parLit "]"
       parLit "<"
       xs ← var ^^$ pManySepBy (parLit ",") parName
       parLit ">"
       parLit "{"
       e₄ ← parSExp
       parLit "}"
       return $ MGaussPE e₁ e₂ e₃ xs e₄
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
