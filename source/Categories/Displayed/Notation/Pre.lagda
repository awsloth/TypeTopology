Anna Williams 14 February 2026

Notation for displayed precategories.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Sets
open import UF.DependentEquality
open import Categories.Pre
open import Categories.Notation.Wild
open import Categories.Notation.Pre
open import Categories.Displayed.Pre

module Categories.Displayed.Notation.Pre where

\end{code}

We now define some notation for displayed precategories similarly to that of
wild categories.

\begin{code}

record DOBJ {𝓤 𝓥 : Universe}
            {P : Precategory 𝓦 𝓣}
            (D : DisplayedPrecategory 𝓤 𝓥 P)
          : ((𝓦 ⊔ 𝓣) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
 field
  obj[_] : obj P → 𝓤 ̇

open DOBJ {{...}} public

module _ {𝓤 𝓥 : Universe}
         {P : Precategory 𝓦 𝓣}
         (D : DisplayedPrecategory 𝓤 𝓥 P) where
 open PrecategoryNotation P

 instance
  d-obj-m : DOBJ D
  obj[_] {{d-obj-m}} = DisplayedPrecategory.obj[_] D

 record DHOM  : ((𝓦 ⊔ 𝓣) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
  field
   hom[_] : {a b : obj P} → hom a b → obj[ a ] → obj[ b ] → 𝓥 ̇

 open DHOM {{...}} public

 instance
  d-hom-m : DHOM
  hom[_] {{d-hom-m}} = DisplayedPrecategory.hom[_] D

 record DCOMP : ((𝓦 ⊔ 𝓣) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
  field
   _∘'_ : {a b c : obj P}
          {g : hom b c}
          {f : hom a b}
          {x : obj[ a ]}
          {y : obj[ b ]}
          {z : obj[ c ]}
          (gyz : hom[ g ] y z)
          (fxy : hom[ f ] x y)
       → hom[ g ○ f ] x z

 open DCOMP {{...}} public

 record DID : ((𝓦 ⊔ 𝓣) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
  field
   disp-id : {c : obj P}
             {x : obj[ c ]}
           → hom[ 𝒊𝒅 ] x x

 open DID {{...}} public

 instance
  dcomp-m : DCOMP
  _∘'_ {{dcomp-m}} = DisplayedPrecategory._∘'_ D


 instance
  d-id-m : DID
  disp-id {{d-id-m}} = DisplayedPrecategory.disp-id D

 record DNotation : ((𝓦 ⊔ 𝓣) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
  field
   hom[-]-is-set : {a b : obj P}
                   {f : hom a b}
                   {x : obj[ a ]}
                   {y : obj[ b ]}
                 → is-set (hom[ f ] x y)
   cmp-right-id : {a b : obj P}
                  {f' : hom a b}
                  {x : obj[ a ]}
                  {y : obj[ b ]}
                  (f : hom[ f' ] x y)
                → f ∘' disp-id
                ＝⟦ (λ - → hom[ - ] x y) , 𝒊𝒅-is-right-neutral f' ⟧
                  f

   cmp-left-id : {a b : obj P}
                 {f' : hom a b}
                 {x : obj[ a ]}
                 {y : obj[ b ]}
                 (f : hom[ f' ] x y)
               → disp-id ∘' f
               ＝⟦ (λ - → hom[ - ] x y) , 𝒊𝒅-is-left-neutral f' ⟧
                 f
  
   cmp-assoc : {a b c d : obj P}
               {f' : hom a b}
               {g' : hom b c}
               {h' : hom c d}
               {x : obj[ a ]}
               {y : obj[ b ]}
               {z : obj[ c ]}
               {w : obj[ d ]}
               {f : hom[ f' ] x y}
               {g : hom[ g' ] y z}
               {h : hom[ h' ] z w}
             → h ∘' (g ∘' f)
             ＝⟦ (λ - → hom[ - ] x w) , assoc f' g' h' ⟧
               (h ∘' g) ∘' f

   is-iso-disp : {c c' : obj P}
            {d : obj[ c ]}
            {d' : obj[ c' ]}
            (isom : c ≅ c')
            (f : hom[ ⌜ isom ⌝ ] d d')
          → 𝓥 ̇
   _≅[_]_ : {c c' : obj P}
            (d : obj[ c ])
            (iso : c ≅ c')
            (d' : obj[ c' ])
          → 𝓥 ̇
   id-to-iso-disp : {c c' : obj P}
                  (e : c ＝ c')
                  (d : obj[ c ])
                  (d' : obj[ c' ])
                  (e' : d ＝⟦ obj[_] , e ⟧ d')
                → d ≅[ id-to-iso c c' e ] d'

 open DNotation {{...}} public


module DisplayedNotation {𝓦 𝓣 : Universe}
                         {P : Precategory 𝓦 𝓣}
                         (D : DisplayedPrecategory 𝓤 𝓥 P) where
 instance
  d-obj : DOBJ D
  obj[_] {{d-obj}} = DisplayedPrecategory.obj[_] D
  

 instance
  d-hom : DHOM D
  hom[_] {{d-hom}} = DisplayedPrecategory.hom[_] D

 instance
  d-id : DID D
  disp-id {{d-id}} = DisplayedPrecategory.disp-id D

 instance
  d-comp : DCOMP D
  _∘'_ {{d-comp}} = DisplayedPrecategory._∘'_ D


 instance
  d-notation : DNotation D
  hom[-]-is-set {{d-notation}} = DisplayedPrecategory.hom[-]-is-set D
  cmp-right-id {{d-notation}} = DisplayedPrecategory.cmp-right-id D
  cmp-left-id {{d-notation}} = DisplayedPrecategory.cmp-left-id D
  cmp-assoc {{d-notation}} = DisplayedPrecategory.cmp-assoc D
  is-iso-disp {{d-notation}} = DisplayedPrecategory.is-iso-disp D
  _≅[_]_ {{d-notation}} = DisplayedPrecategory._≅[_]_ D
  id-to-iso-disp {{d-notation}} = DisplayedPrecategory.id-to-iso-disp D
  

\end{code}


