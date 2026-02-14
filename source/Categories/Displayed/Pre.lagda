Anna Williams, 28 October 2025

Definition of a displayed category.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.DependentEquality
open import UF.Equiv hiding (_≅_ ; inverse ; ⌜_⌝)
open import UF.Sets
open import Categories.Pre
open import Categories.Notation.Pre

module Categories.Displayed.Pre where


\end{code}

We first define the notion of a displayed precategory. The objects and homs of
this are indexed by a given base precategory. We then derive the other parts of
a precategory, including the usual axioms which now have dependent equalities.

\begin{code}

record DisplayedPrecategory (𝓦 𝓣 : Universe)
                            (P : Precategory 𝓤 𝓥)
                          : (𝓦 ⊔ 𝓣 ⊔ 𝓤 ⊔ 𝓥)⁺ ̇  where
 open PrecategoryNotation P
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
          → hom[ 𝒊𝒅 ] x x

  _∘'_ : {a b c : obj P}
         {g : hom b c}
         {f : hom a b}
         {x : obj[ a ]}
         {y : obj[ b ]}
         {z : obj[ c ]}
         (gyz : hom[ g ] y z)
         (fxy : hom[ f ] x y)
       → hom[ g ○ f ] x z

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
               → f ∘' disp-id ＝⟦ hom[-] x y , 𝒊𝒅-is-right-neutral f' ⟧ f

  cmp-left-id : {a b : obj P}
                {f' : hom a b}
                {x : obj[ a ]}
                {y : obj[ b ]}
                (f : hom[ f' ] x y)
              → disp-id ∘' f ＝⟦ hom[-] x y , 𝒊𝒅-is-left-neutral f' ⟧ f
  
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
            (e : c ≅ c')
            (f : hom[ ⌜ e ⌝ ] d d')
          → 𝓣 ̇
 is-iso-disp {c} {c'} {d} {d'} e f
   = Σ g ꞉ hom[ ⌞ underlying-morphism-is-isomorphism e ⌟ ] d' d
     , ((g ∘' f ＝⟦ hom[-] d d , ⌞ underlying-morphism-is-isomorphism e ⌟-is-left-inverse ⟧ disp-id)
       × (f ∘' g ＝⟦ hom[-] d' d' , ⌞ underlying-morphism-is-isomorphism e ⌟-is-right-inverse ⟧ disp-id))

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
   h : disp-id ∘' disp-id ＝⟦ hom[-] d d , 𝒊𝒅-is-left-neutral 𝒊𝒅 ⟧ disp-id
   h = cmp-left-id disp-id

\end{code}
