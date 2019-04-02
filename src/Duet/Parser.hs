module Duet.Parser where

import Duet.UVMHS

import Duet.Syntax
import Duet.RNF
import Duet.Quantity

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
  ["let","in","sλ","pλ","return","on"
  ,"ℕ","ℝ","ℝ⁺","𝔻","𝕀","𝕄","𝔻𝔽","𝔹","𝕊","★","∷","⋅","[]","⧺"
  ,"LR","L2","U"
  ,"real","bag","set","record", "unionAll"
  ,"partitionDF","addColDF","mapDF","join₁","joinDF₁","parallel"
  ,"chunks","mfold-row","mfilter","zip"
  ,"matrix","mcreate","mclip","clip","∇","U∇","mmap","bmap","idx","℘","𝐝","conv","disc","∈"
  ,"aloop","loop","gauss","mgauss","bgauss","laplace","mlaplace","mconv","×","tr"
  ,"rows","cols","exponential","rand-resp"
  ,"sample","rand-nat"
  ,"L1","L2","L∞","U"
  ,"dyn","real"
  ,"ZCDP","RENYI"
  ,"box","unbox","boxed"
  ,"if","then","else"
  ,"true","false"
  ,"CSVtoMatrix"
  ]

tokPunctuation ∷ 𝐿 𝕊
tokPunctuation = list
  ["=",":","@",".","⇒","→","←","#","↦","≡","⧼","⧽"
  ,"[","]","(",")","{","}","<",">",",",";","|","⟨","⟩"
  ,"⊔","⊓","+","⋅","/","√","㏒"
  ,"-","%","≟"
  ,"×","&","⊸","⊸⋆"
  ,"∧","∨"
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
parKind = pNew "kind" $ tries
  [ do parLit "ℕ" ; return ℕK
  , do parLit "ℝ⁺" ; return ℝK
  ]

parRowsT :: Parser Token (RowsT RExp)
parRowsT = tries
  [ do const StarRT ^$ parLit "★"
  , do η ← parRExp; return $ RexpRT η
  ]

parMExp ∷ (PRIV_C p) ⇒ PRIV_W p → Parser Token (MExp RExp)
parMExp mode = mixfixParser $ concat
  [ mix $ MixTerminal $ const EmptyME ^$ parLit "[]"
  , mix $ MixPrefix 6 $ do
      τ ← parType mode
      parLit "∷"
      return $ \ me → ConsME τ me
  , mix $ MixInfixL 3 $ do
      parLit "⧺"
      return AppendME
  , mix $ MixTerminal $ do
      r ← parRExp
      parLit "⋅"
      τ ← parType mode
      return $ RexpME r τ
  , mix $ MixTerminal $ VarME ^$ parVar
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

parPriv ∷ PRIV_W p → Parser Token (Priv p RExp)
parPriv = undefined

parSpace ∷ Parser Token ()
parSpace = pSkip (const False) $ void $ pOneOrMore $ tries
  [ pLit TokenComment
  , pLit TokenSpace
  ]

parTypeSource ∷ (PRIV_C p) ⇒ PRIV_W p → Parser Token (TypeSource RExp)
parTypeSource p = pWithContext "type" (parType p)

parType ∷ (PRIV_C p) ⇒ PRIV_W p → Parser Token (Type RExp)
parType mode = mixfixParser $ concat
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
  , mix $ MixTerminal $ const 𝔹T ^$ parLit "𝔹"
  , mix $ MixTerminal $ const 𝕊T ^$ parLit "𝕊"
  , mix $ MixTerminal $ do
      parLit "𝕀"
      parLit "["
      η ← parRExp
      parLit "]"
      return $ 𝕀T η
  , mix $ MixTerminal $ do
      parLit "𝕄"
      parLit "["
      ℓ ← parNorm
      parLit ","
      c ← parClip
      parLit "|"
      ηₘ ← parRowsT
      parLit ","
      ηₙ ← parMExp mode
      parLit "]"
      return $ 𝕄T ℓ c ηₘ ηₙ
  , mix $ MixTerminal $ do
      parLit "𝔻"
      return $ 𝔻T ℝT
  , mix $ MixTerminal $ do
      parLit "𝔻𝔽"
      parLit "["
      as ← pOneOrMoreSepBy (parLit ",") $ do
        a ← parName
        parLit ":"
        τ ← parType mode
        return $ a :* τ
      parLit "]"
      -- TODO: support parsing sensitivity and clip
      return $ BagT L1 UClip (RecordT as)
  , mix $ MixTerminal $ do
      parLit "record"
      parLit "["
      as ← pOneOrMoreSepBy (parLit ",") $ do
        a ← parName
        parLit ":"
        τ ← parType mode
        return $ a :* τ
      parLit "]"
      return $ RecordT as
  , mix $ MixTerminal $ do
      parLit "℘"
      parLit "("
      τ ← parType mode
      parLit ")"
      return $ SetT τ
  -- TODO: support parsing sensitivity and clip
  , mix $ MixPrefix 6 $ const (BagT L1 UClip) ^$ parLit "bag"
  , mix $ MixPrefix 6 $ const (𝔻T) ^$ parLit "𝐝"
  , mix $ MixInfixL 3 $ const (:+:) ^$ parLit "+"
  , mix $ MixInfixL 4 $ const (:×:) ^$ parLit "×"
  , mix $ MixInfixL 4 $ const (:&:) ^$ parLit "&"
  , mix $ MixPrefix 2 $ do
      parLit "∀"
      ακs ← pOneOrMoreSepBy (parLit ",") $ do
        α ← parVar
        parLit ":"
        κ ← parKind
        return $ α :* κ
      parLit "."
      τ₁ ← parType mode
      parLit "⊸"
      parLit "["
      s ← parSens
      parLit "]"
      return $ \ τ₂ → (ακs :* τ₁) :⊸: (s :* τ₂)
  , mix $ MixPrefix 2 $ do
      parLit "∀"
      ακs ← pOneOrMoreSepBy (parLit ",") $ do
        α ← parVar
        parLit ":"
        κ ← parKind
        return $ α :* κ
      parLit "."
      τps ← pOneOrMoreSepBy (parLit ",") $ do
        τ ← parType mode
        parLit "@"
        p ← parPriv mode
        return $ τ :* p
      return $ (:⊸⋆:) $ ακs :* PArgs τps
  ]

parGrad ∷ Parser Token Grad
parGrad = tries
  [ const LR ^$ parLit "LR"
  ]

parSExp ∷ (PRIV_C p) ⇒ PRIV_W p → Parser Token (SExpSource p)
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
  , mixF $ MixFTerminal $ do
      parLit "true"
      return $ TrueSE
  , mixF $ MixFTerminal $ do
      parLit "false"
      return $ FalseSE
  , mixF $ MixFPrefix 10 $ const DynSE ^$ parLit "dyn"
  , mixF $ MixFTerminal $ ℕSE ^$ parNat
  , mixF $ MixFTerminal $ ℝSE ^$ parDbl
  , mixF $ MixFPrefix 10 $ const RealSE ^$ parLit "real"
  , mixF $ MixFInfixL 3 $ const MaxSE ^$ parLit "⊔"
  , mixF $ MixFInfixL 4 $ const MinSE ^$ parLit "⊓"
  , mixF $ MixFInfixL 5 $ const PlusSE ^$ parLit "+"
  , mixF $ MixFInfixL 6 $ const TimesSE ^$ parLit "⋅"
  , mixF $ MixFInfixL 6 $ const MTimesSE ^$ parLit "×"
  , mixF $ MixFInfixL 7 $ const DivSE ^$ parLit "/"
  , mixF $ MixFPrefix 8 $ const RootSE ^$ parLit "√"
  , mixF $ MixFPrefix 8 $ const LogSE ^$ parLit "㏒"
  , mixF $ MixFInfixL 7 $ const ModSE ^$ parLit "%"
  , mixF $ MixFInfixL 5 $ const MinusSE ^$ parLit "-"
  , mixF $ MixFInfixL 2 $ const MinusSE ^$ parLit "≟"
  , mixF $ MixFInfixL 2 $ const EqualsSE ^$ parLit "≡"
  , mixF $ MixFInfixL 2 $ const MemberSE ^$ parLit "∈"
  , mixF $ MixFInfixL 1 $ const AndSE ^$ parLit "∧"
  , mixF $ MixFInfixL 1 $ const OrSE ^$ parLit "∨"
  , mixF $ MixFPostfix 10 $ do
      parLit "⧼"
      a ← parName
      parLit "⧽"
      return $ RecordColSE a
  , mixF $ MixFTerminal $ do
      parLit "mfilter"
      e₁ ← parSExp p
      parLit "{"
      x ← parVar
      parLit "⇒"
      e₂ ← parSExp p
      parLit "}"
      return $ MFilterSE e₁ x e₂
  , mixF $ MixFTerminal $ do
      parLit "mapDF"
      e₁ ← parSExp p
      parLit "{"
      x ← parVar
      parLit "⇒"
      e₂ ← parSExp p
      parLit "}"
      return $ DFMapSE e₁ x e₂
  , mixF $ MixFTerminal $ do
      parLit "join₁"
      parLit "["
      e₁ ← parSExp p
      parLit ","
      e₂ ← parSExp p
      parLit ","
      e₃ ← parSExp p
      parLit ","
      e₄ ← parSExp p
      parLit "]"
      return $ JoinSE e₁ e₂ e₃ e₄
  , mixF $ MixFPrefix 10 $ do
      parLit "addColDF"
      parLit "⧼"
      x ← parName
      parLit "⧽"
      return $ DFAddColSE x
  , mixF $ MixFTerminal $ do
      parLit "partitionDF"
      parLit "["
      e₁ ← parSExp p
      parLit ","
      a ← parName
      parLit ","
      e₂ ← parSExp p
      parLit "]"
      return $ DFPartitionSE e₁ a e₂
  , mixF $ MixFTerminal $ do
      parLit "joinDF₁"
      parLit "⧼"
      x ← parName
      parLit "⧽"
      parLit "["
      e₁ ← parSExp p
      parLit ","
      e₂ ← parSExp p
      parLit "]"
      return $ DFJoin1SE x e₁ e₂
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
  -- , mixF $ MixFTerminal $ do
  --   parLit "CSVtoMatrix"
  --   parLit "("
  --   f ← parName
  --   parLit ","
  --   τ ← parTypeSource p
  --   parLit ")"
  --   return $ CSVtoMatrixSE f τ
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
  , mixF $ MixFPrefix 10 $ const MTransposeSE ^$ parLit "tr"
  , mixF $ MixFPrefix 10 $ const IdxSE ^$ parLit "idx"
  , mixF $ MixFPrefix 10 $ do
      parLit "mclip"
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
      parLit "U∇"
      parLit "["
      g ← parGrad
      parLit "|"
      e₁ ← parSExp p
      parLit ";"
      e₂ ← parSExp p
      parLit ","
      e₃ ← parSExp p
      parLit "]"
      return $ MUnbGradSE g e₁ e₂ e₃
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
  , mixF $ MixFTerminal $ do
      parLit "mfold-row"
      e₁ ← parSExp p
      parLit ","
      e₂ ← parSExp p
      parLit "{"
      x₁ ← parVar
      parLit ","
      x₂ ← parVar
      parLit "⇒"
      e₃ ← parSExp p
      parLit "}"
      return $ MFoldSE e₁ e₂ x₁ x₂ e₃
  , mixF $ MixFTerminal $ do
      parLit "bmap"
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
        None → BMapSE e₁ x₁ e₃
        Some (e₂ :* x₂) → BMap2SE e₁ e₂ x₁ x₂ e₃
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
  , mixF $ MixFInfixL 10 $ const (\ e₁ e₂ → AppSE e₁ Nil e₂) ^$ parSpace
  , mixF $ MixFTerminal $ do
       e₁ ← parSExp p
       parLit "@"
       parLit "["
       ks ← pManySepBy (parLit ",") $ parRExp
       parLit "."
       e₂ ← parSExp p
       parLit "]"
       return $ AppSE e₁ ks e₂
  , mixF $ MixFPrefix 1 $ do
      parLit "sλ"
      ακs ← pManySepBy (parLit ",") $ do
        α ← parVar
        parLit ":"
        κ ← parKind
        return $ α :* κ
      parLit "."
      x ← parVar
      parLit ":"
      τ ← parTypeSource p
      xτs ← pMany $ do
        parLit ","
        x' ← parVar
        parLit ":"
        τ' ← parTypeSource p
        return $ x' :* τ'
      parLit "⇒"
      return $ \ e →
        let ecxt = annotatedTag e
        in SFunSE ακs x τ $ foldr e (\ (x' :* τ') e' → Annotated ecxt $ SFunSE Nil x' τ' e') xτs
  , mixF $ MixFTerminal $ do
      parLit "pλ"
      ακs ← pManySepBy (parLit ",") $ do
        α ← parVar
        parLit ":"
        κ ← parKind
        return $ α :* κ
      parLit "."
      xτs ← pOneOrMoreSepBy (parLit ",") $ do
        x ← parVar
        parLit ":"
        τ ← parTypeSource p
        return $ x :* τ
      parLit "⇒"
      e ← parPExp p
      return $ PFunSE ακs xτs e
  , mixF $ MixFTerminal $ do
      parLit "℘"
      parLit "{"
      ses ← pManySepBy (parLit ",") $ parSExp p
      parLit "}"
      return $ SetSE ses
  , mixF $ MixFTerminal $ do
      parLit "unionAll"
      e ← parSExp p
      return $ UnionAllSE e
  , mixF $ MixFTerminal $ do
       parLit "⟨"
       e₁ ← parSExp p
       parLit ","
       e₂ ← parSExp p
       parLit "⟩"
       return $ TupSE e₁ e₂
  , mixF $ MixFTerminal $ do
       parLit "loop"
       e₂ ← parSExp p
       parLit "on"
       e₃ ← parSExp p
       parLit "{"
       x₁ ← parVar
       parLit ","
       x₂ ← parVar
       parLit "⇒"
       e₄ ← parSExp p
       parLit "}"
       return $ LoopSE e₂ e₃ x₁ x₂ e₄
  , mixF $ MixFTerminal $ do
       parLit "chunks"
       parLit "["
       e₁ ← parSExp p
       parLit ","
       e₂ ← parSExp p
       parLit ","
       e₃ ← parSExp p
       parLit "]"
       return $ ChunksSE e₁ e₂ e₃
  , mixF $ MixFTerminal $ do
       parLit "zip"
       parLit "["
       e₁ ← parSExp p
       parLit ","
       e₂ ← parSExp p
       parLit "]"
       return $ MZipSE e₁ e₂
  , mixF $ MixFPrefix 10 $ const BoxSE ^$ parLit "box"
  , mixF $ MixFPrefix 10 $ const UnboxSE ^$ parLit "unbox"
  , mixF $ MixFPrefix 10 $ const ClipSE ^$ parLit "clip"
  , mixF $ MixFPrefix 10 $ const ConvSE ^$ parLit "conv"
  , mixF $ MixFPrefix 10 $ const MConvertSE ^$ parLit "mconv"
  , mixF $ MixFPrefix 10 $ const DiscSE ^$ parLit "disc"
  ]

parPExp ∷ (PRIV_C p) ⇒ PRIV_W p → Parser Token (PExpSource p)
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
  , do e ← parSExp p
       parLit "@"
       parLit "["
       ks ← pManySepBy (parLit ",") $ parRExp
       parLit "."
       xs ← pManySepBy (parLit ",") $ parSExp p
       parLit "]"
       return $ AppPE e ks xs
  , do x ← parVar
       parLit "←"
       e₁ ← parPExp p
       parLit ";"
       e₂ ← parPExp p
       return $ BindPE x e₁ e₂
  , do parLit "if"
       e₁ ← parSExp p
       parLit "then"
       parLit "{"
       e₂ ← parPExp p
       parLit "}"
       parLit "else"
       parLit "{"
       e₃ ← parPExp p
       parLit "}"
       return $ IfPE e₁ e₂ e₃
  , do parLit "parallel"
       parLit "["
       e₁ ← parSExp p
       parLit ","
       e₂ ← parSExp p
       parLit "]"
       parLit "{"
       x₁ ← parVar
       parLit "⇒"
       e₃ ← parSExp p
       parLit "}"
       parLit "{"
       x₂ ← parVar
       parLit ","
       x₃ ← parVar
       parLit "⇒"
       e₄ ← parPExp p
       parLit "}"
       return $ ParallelPE e₁ e₂ x₁ e₃ x₂ x₃ e₄
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
      _ → abort
  , do parLit "loop"
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
      RENYI_W → do
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
        return $ MGaussPE e₁ (RenyiGaussParams e₂ e₃) xs e₄
      TC_W → do
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
        return $ MGaussPE e₁ (TCGaussParams e₂ e₃) xs e₄
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
        parLit "bgauss"
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
        return $ BGaussPE e₁ (EDGaussParams e₂ e₃) xs e₄
      RENYI_W → do
        parLit "bgauss"
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
        return $ BGaussPE e₁ (RenyiGaussParams e₂ e₃) xs e₄
      ZC_W → do
        parLit "bgauss"
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
        return $ BGaussPE e₁ (ZCGaussParams e₂) xs e₄
      _ → abort
  , case p of
      EPS_W → do
        parLit "laplace"
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
        return $ LaplacePE e₁ (EpsLaplaceParams e₂) xs e₃
      _ → abort
  , case p of
      ED_W → do
        parLit "gauss"
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
        return $ GaussPE e₁ (EDGaussParams e₂ e₃) xs e₄
      RENYI_W → do
        parLit "gauss"
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
        return $ GaussPE e₁ (RenyiGaussParams e₂ e₃) xs e₄
      ZC_W → do
        parLit "gauss"
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
        return $ GaussPE e₁ (ZCGaussParams e₂) xs e₄
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
        return $ EDSamplePE e₁ e₂ e₃ x₁ x₂ e₄
      RENYI_W → do
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
        return $ RenyiSamplePE e₁ e₂ e₃ x₁ x₂ e₄
      TC_W → do
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
        return $ TCSamplePE e₁ e₂ e₃ x₁ x₂ e₄
      _ → abort
  , do parLit "rand-nat"
       parLit "["
       e₁ ← parSExp p
       parLit ","
       e₂ ← parSExp p
       parLit "]"
       return $ RandNatPE e₁ e₂
  , case p of
      ED_W → tries
        [ do parLit "ZCDP"
             parLit "["
             e₁ ← parSExp ED_W
             parLit "]"
             parLit "{"
             e₂ ← parPExp ZC_W
             parLit "}"
             return $ ConvertZCEDPE e₁ e₂
        , do parLit "RENYI"
             parLit "["
             e₁ ← parSExp ED_W
             parLit "]"
             parLit "{"
             e₂ ← parPExp RENYI_W
             parLit "}"
             return $ ConvertRENYIEDPE e₁ e₂
        ]
      _ → abort
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
