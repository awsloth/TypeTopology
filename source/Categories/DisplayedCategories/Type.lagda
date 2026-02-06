Anna Williams, 28 October 2025

Definition of a displayed category.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_∘_ ; id)
open import Notation.UnderlyingType
open import UF.Base
open import UF.DependentEquality
open import UF.Equiv hiding (_≅_ ; _≅⟨_⟩_)
open import UF.Sets
open import UF.Sets-Properties

module Categories.DisplayedCategories.Type where

open import Categories.Type 

\end{code}

We first define the notion of a displayed precategory. The objects and homs of
this are indexed by a given base precategory. We then derive the other parts of
a precategory, including the usual axioms which now have dependent equalities.

\begin{code}

record DisplayedPrecategory (𝓦 𝓣 : Universe)
                            (P : Precategory 𝓤 𝓥)
                          : ((𝓦 ⊔ 𝓣) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
 open CategoryNotation ⟨ P ⟩
 field
  obj[_] : (c : obj P) → 𝓦 ̇
  hom[_] : {a b : obj P}
           (f : hom a b)
           (x : obj[ a ])
           (y : obj[ b ])
         → 𝓣 ̇
  hom[-]-is-set : {a b : obj P}
                  {f : hom a b}
                  {x : obj[ a ]}
                  {y : obj[ b ]}
                → is-set (hom[ f ] x y)
  
  disp-id : {c : obj P}
            {x : obj[ c ]}
          → hom[ id ] x x

  _∘'_ : {a b c : obj P}
         {g : hom b c}
         {f : hom a b}
         {x : obj[ a ]}
         {y : obj[ b ]}
         {z : obj[ c ]}
         (gyz : hom[ g ] y z)
         (fxy : hom[ f ] x y)
       → hom[ g ∘ f ] x z

 private
  hom[-] : {a b : obj P}
           (x : obj[ a ])
           (y : obj[ b ])
         → hom a b → 𝓣 ̇
  hom[-] x y = λ - → hom[ - ] x y

 field
  cmp-right-id : {a b : obj P}
                 {f' : hom a b}
                 {x : obj[ a ]}
                 {y : obj[ b ]}
                 (f : hom[ f' ] x y)
               → f ∘' disp-id ＝⟦ hom[-] x y , right-id f' ⟧ f

  cmp-left-id : {a b : obj P}
                {f' : hom a b}
                {x : obj[ a ]}
                {y : obj[ b ]}
                (f : hom[ f' ] x y)
              → disp-id ∘' f ＝⟦ hom[-] x y , left-id f' ⟧ f
  
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
            ＝⟦ hom[-] x w , assoc f' g' h' ⟧
              (h ∘' g) ∘' f

\end{code}

We can now define a displayed version of isomorphism between objects.

\begin{code}

 is-iso-disp : {c c' : obj P}
            {d : obj[ c ]}
            {d' : obj[ c' ]}
            (isom : c ≅ c')
            (f : hom[ iso isom ] d d')
          → 𝓣 ̇
 is-iso-disp {c} {c'} {d} {d'} isom f
   = Σ g ꞉ hom[ inv (isomorphism-proof isom) ] d' d
     , ((g ∘' f ＝⟦ hom[-] d d , l-inv (isomorphism-proof isom) ⟧ disp-id)
       × (f ∘' g ＝⟦ hom[-] d' d' , r-inv (isomorphism-proof isom) ⟧ disp-id))

 _≅[_]_ : {c c' : obj P}
          (d : obj[ c ])
          (iso : c ≅ c')
          (d' : obj[ c' ])
        → 𝓣 ̇
 d ≅[ iso ] d' = Σ f ꞉ hom[ pr₁ iso ] d d' , is-iso-disp iso f
       
\end{code}

Following the definition of isomorphism, as with categories we can now define
the notion of id-to-iso for displayed precategories and thus define displayed
categories.

\begin{code}

 id-to-iso-disp : {c c' : obj P}
                  (e : c ＝ c')
                  (d : obj[ c ])
                  (d' : obj[ c' ])
                  (e' : d ＝⟦ obj[_] , e ⟧ d')
                → d ≅[ id-to-iso c c' e ] d'
 id-to-iso-disp refl d _ refl = disp-id , disp-id , h , h
  where
   h : disp-id ∘' disp-id ＝⟦ hom[-] d d , left-id id ⟧ disp-id
   h = cmp-left-id disp-id

 is-disp-category : (𝓤 ⊔ 𝓦 ⊔ 𝓣) ̇
 is-disp-category = {c c' : obj P}
                    (e : c ＝ c')
                    (d : obj[ c ])
                    (d' : obj[ c' ])
                  → is-equiv (id-to-iso-disp e d d')

\end{code}

We now define some notation for displayed precategories similarly to that of
wild categories.

\begin{code}

open DisplayedPrecategory public using (is-disp-category)

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
 open CategoryNotation ⟨ P ⟩

 instance
  d-obj-m : DOBJ D
  obj[_] {{d-obj-m}} = DisplayedPrecategory.obj[_] D

 record DHOM  : ((𝓦 ⊔ 𝓣) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
  field
   hom[_] : {a b : obj ⟨ P ⟩} → hom a b → obj[ a ] → obj[ b ] → 𝓥 ̇

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
       → hom[ g ∘ f ] x z

 open DCOMP {{...}} public

 record DID : ((𝓦 ⊔ 𝓣) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
  field
   disp-id : {c : obj P}
             {x : obj[ c ]}
           → hom[ id ] x x

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
                ＝⟦ (λ - → hom[ - ] x y) , right-id f' ⟧
                  f

   cmp-left-id : {a b : obj P}
                 {f' : hom a b}
                 {x : obj[ a ]}
                 {y : obj[ b ]}
                 (f : hom[ f' ] x y)
               → disp-id ∘' f
               ＝⟦ (λ - → hom[ - ] x y) , left-id f' ⟧
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
            (f : hom[ iso isom ] d d')
          → 𝓥 ̇
   _≅[_]_ : {c c' : obj P}
            (d : obj[ c ])
            (iso : c ≅ c')
            (d' : obj[ c' ])
          → 𝓥 ̇

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

\end{code}

We can now define a total precategory.

\begin{code}

TotalPrecategory : {𝓦 𝓨 : Universe}
                   {C : Precategory 𝓤 𝓥}
                   (D : DisplayedPrecategory 𝓦 𝓨 C)
                 → Precategory (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓨)
TotalPrecategory {𝓤} {𝓥} {𝓦} {𝓨} {C} D = (wildcategory , total-is-precategory)
 where
  open CategoryNotation ⟨ C ⟩
  open DisplayedNotation D

  wildcategory : WildCategory (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓨)
  wildcategory = wildcat-make (Σ c ꞉ obj C , obj[ c ])
                              (λ (a , x) (b , y) → Σ f ꞉ hom a b , hom[ f ] x y)
                              (id , disp-id)
                              (λ (g' , g) (f' , f) → g' ∘ f' , g ∘' f)
                              (λ (f' , f) → to-Σ-＝ (left-id f'
                                          , Idtofun (did _ _) (cmp-left-id f)))
                              (λ (f' , f) → to-Σ-＝ (right-id f'
                                          , Idtofun (did _ _) (cmp-right-id f)))
                              (λ f g h → to-Σ-＝ (assoc _ _ _
                                       , Idtofun (did _ _) cmp-assoc))
   where
    did = dependent-Id-via-transport

  total-is-precategory : is-precategory wildcategory
  total-is-precategory _ _ = Σ-is-set (hom-is-set C) (λ _ → hom[-]-is-set)

\end{code}

We now look at displayed categories. These are exactly precategories
such that following map, id-to-iso-disp is an eqivalence.

\begin{code}

DisplayedCategory : (𝓤 𝓥 : Universe)
                    {𝓦 𝓣 : Universe}
                    (P : Precategory 𝓦 𝓣)
                  → (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣) ⁺ ̇
DisplayedCategory 𝓤 𝓥 P = Σ D ꞉ DisplayedPrecategory 𝓤 𝓥 P , is-disp-category D

\end{code}
