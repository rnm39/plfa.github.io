---
title     : "More: Additional constructs of simply-typed lambda calculus"
permalink : /More/
---

```agda
module plfa.part2.More where
```

So far, we have focussed on a relatively minimal language, based on
Plotkin's PCF, which supports functions, naturals, and fixpoints.  In
this chapter we extend our calculus to support the following:

  * primitive numbers
  * _let_ bindings
  * products
  * an alternative formulation of products
  * sums
  * unit type
  * an alternative formulation of unit type
  * empty type
  * lists

All of the data types should be familiar from Part I of this textbook.
For _let_ and the alternative formulations we show how they translate
to other constructs in the calculus.  Most of the description will be
informal. We show how to formalise the first four constructs and leave
the rest as an exercise for the reader.

Our informal descriptions will be in the style of
Chapter [Lambda](/Lambda/),
using extrinsically-typed terms,
while our formalisation will be in the style of
Chapter [DeBruijn](/DeBruijn/),
using intrinsically-typed terms.

By now, explaining with symbols should be more concise, more precise,
and easier to follow than explaining in prose.
For each construct, we give syntax, typing, reductions, and an example.
We also give translations where relevant; formally establishing the
correctness of translations will be the subject of the next chapter.

## Primitive numbers

We define a `Nat` type equivalent to the built-in natural number type
with multiplication as a primitive operation on numbers:

### Syntax

    A, B, C ::= ...                     Types
      Nat                                 primitive natural numbers

    L, M, N ::= ...                     Terms
      con c                               constant
      L `* M                              multiplication

    V, W ::= ...                        Values
      con c                               constant

### Typing

The hypothesis of the `con` rule is unusual, in that
it refers to a typing judgment of Agda rather than a
typing judgment of the defined calculus:

    c : ℕ
    --------------- con
    Γ ⊢ con c : Nat

    Γ ⊢ L : Nat
    Γ ⊢ M : Nat
    ---------------- _`*_
    Γ ⊢ L `* M : Nat

### Reduction

A rule that defines a primitive directly, such as the last rule below,
is called a δ rule.  Here the δ rule defines multiplication of
primitive numbers in terms of multiplication of naturals as given
by the Agda standard prelude:

    L —→ L′
    ----------------- ξ-*₁
    L `* M —→ L′ `* M

    M —→ M′
    ----------------- ξ-*₂
    V `* M —→ V `* M′

    ----------------------------- δ-*
    con c `* con d —→ con (c * d)

### Example

Here is a function to cube a primitive number:

    cube : ∅ ⊢ Nat ⇒ Nat
    cube = ƛ x ⇒ x `* x `* x


## Let bindings

Let bindings affect only the syntax of terms; they introduce no new
types or values:

### Syntax

    L, M, N ::= ...                     Terms
      `let x `= M `in N                   let

### Typing

    Γ ⊢ M ⦂ A
    Γ , x ⦂ A ⊢ N ⦂ B
    ------------------------- `let
    Γ ⊢ `let x `= M `in N ⦂ B

### Reduction

    M —→ M′
    --------------------------------------- ξ-let
    `let x `= M `in N —→ `let x `= M′ `in N

    --------------------------------- β-let
    `let x `= V `in N —→ N [ x := V ]

### Example

Here is a function to raise a primitive number to the tenth power:

    exp10 : ∅ ⊢ Nat ⇒ Nat
    exp10 = ƛ x ⇒ `let x2  `= x  `* x  `in
                  `let x4  `= x2 `* x2 `in
                  `let x5  `= x4 `* x  `in
                  x5 `* x5

### Translation

We can translate each _let_ term into an application of an abstraction:

    (`let x `= M `in N) †  =  (ƛ x ⇒ (N †)) · (M †)

Here `M †` is the translation of term `M` from a calculus with the
construct to a calculus without the construct.


## Products {#products}

### Syntax

    A, B, C ::= ...                     Types
      A `× B                              product type

    L, M, N ::= ...                     Terms
      `⟨ M , N ⟩                          pair
      `proj₁ L                            project first component
      `proj₂ L                            project second component

    V, W ::= ...                        Values
      `⟨ V , W ⟩                          pair

### Typing

    Γ ⊢ M ⦂ A
    Γ ⊢ N ⦂ B
    ----------------------- `⟨_,_⟩ or `×-I
    Γ ⊢ `⟨ M , N ⟩ ⦂ A `× B

    Γ ⊢ L ⦂ A `× B
    ---------------- `proj₁ or `×-E₁
    Γ ⊢ `proj₁ L ⦂ A

    Γ ⊢ L ⦂ A `× B
    ---------------- `proj₂ or `×-E₂
    Γ ⊢ `proj₂ L ⦂ B

### Reduction

    M —→ M′
    ------------------------- ξ-⟨,⟩₁
    `⟨ M , N ⟩ —→ `⟨ M′ , N ⟩

    N —→ N′
    ------------------------- ξ-⟨,⟩₂
    `⟨ V , N ⟩ —→ `⟨ V , N′ ⟩

    L —→ L′
    --------------------- ξ-proj₁
    `proj₁ L —→ `proj₁ L′

    L —→ L′
    --------------------- ξ-proj₂
    `proj₂ L —→ `proj₂ L′

    ---------------------- β-proj₁
    `proj₁ `⟨ V , W ⟩ —→ V

    ---------------------- β-proj₂
    `proj₂ `⟨ V , W ⟩ —→ W

### Example

Here is a function to swap the components of a pair:

    swap× : ∅ ⊢ A `× B ⇒ B `× A
    swap× = ƛ z ⇒ `⟨ `proj₂ z , `proj₁ z ⟩


## Alternative formulation of products

There is an alternative formulation of products, where in place of two
ways to eliminate the type we have a case term that binds two
variables.  We repeat the syntax in full, but only give the new type
and reduction rules:

### Syntax

    A, B, C ::= ...                     Types
      A `× B                              product type

    L, M, N ::= ...                     Terms
      `⟨ M , N ⟩                          pair
      case× L [⟨ x , y ⟩⇒ M ]             case

    V, W ::=                            Values
      `⟨ V , W ⟩                          pair

### Typing

    Γ ⊢ L ⦂ A `× B
    Γ , x ⦂ A , y ⦂ B ⊢ N ⦂ C
    ------------------------------- case× or ×-E
    Γ ⊢ case× L [⟨ x , y ⟩⇒ N ] ⦂ C

### Reduction

    L —→ L′
    --------------------------------------------------- ξ-case×
    case× L [⟨ x , y ⟩⇒ N ] —→ case× L′ [⟨ x , y ⟩⇒ N ]

    --------------------------------------------------------- β-case×
    case× `⟨ V , W ⟩ [⟨ x , y ⟩⇒ N ] —→ N [ x := V ][ y := W ]

### Example

Here is a function to swap the components of a pair rewritten in the new notation:

    swap×-case : ∅ ⊢ A `× B ⇒ B `× A
    swap×-case = ƛ z ⇒ case× z
                         [⟨ x , y ⟩⇒ `⟨ y , x ⟩ ]

### Translation

We can translate the alternative formulation into the one with projections:

      (case× L [⟨ x , y ⟩⇒ N ]) †
    =
      `let z `= (L †) `in
      `let x `= `proj₁ z `in
      `let y `= `proj₂ z `in
      (N †)

Here `z` is a variable that does not appear free in `N`.  We refer
to such a variable as _fresh_.

One might think that we could instead use a more compact translation:

    -- WRONG
      (case× L [⟨ x , y ⟩⇒ N ]) †
    =
      (N †) [ x := `proj₁ (L †) ] [ y := `proj₂ (L †) ]

But this behaves differently.  The first term always reduces `L`
before `N`, and it computes `` `proj₁ `` and `` `proj₂ `` exactly once.  The
second term does not reduce `L` to a value before reducing `N`, and
depending on how many times and where `x` and `y` appear in `N`, it
may reduce `L` many times or not at all, and it may compute `` `proj₁ ``
and `` `proj₂ `` many times or not at all.

We can also translate back the other way:

    (`proj₁ L) ‡  =  case× (L ‡) [⟨ x , y ⟩⇒ x ]
    (`proj₂ L) ‡  =  case× (L ‡) [⟨ x , y ⟩⇒ y ]

## Sums {#sums}

### Syntax

    A, B, C ::= ...                     Types
      A `⊎ B                              sum type

    L, M, N ::= ...                     Terms
      `inj₁ M                             inject first component
      `inj₂ N                             inject second component
      case⊎ L [inj₁ x ⇒ M |inj₂ y ⇒ N ]    case

    V, W ::= ...                        Values
      `inj₁ V                             inject first component
      `inj₂ W                             inject second component

### Typing

    Γ ⊢ M ⦂ A
    -------------------- `inj₁ or ⊎-I₁
    Γ ⊢ `inj₁ M ⦂ A `⊎ B

    Γ ⊢ N ⦂ B
    -------------------- `inj₂ or ⊎-I₂
    Γ ⊢ `inj₂ N ⦂ A `⊎ B

    Γ ⊢ L ⦂ A `⊎ B
    Γ , x ⦂ A ⊢ M ⦂ C
    Γ , y ⦂ B ⊢ N ⦂ C
    ----------------------------------------- case⊎ or ⊎-E
    Γ ⊢ case⊎ L [inj₁ x ⇒ M |inj₂ y ⇒ N ] ⦂ C

### Reduction

    M —→ M′
    ------------------- ξ-inj₁
    `inj₁ M —→ `inj₁ M′

    N —→ N′
    ------------------- ξ-inj₂
    `inj₂ N —→ `inj₂ N′

    L —→ L′
    ---------------------------------------------------------------------- ξ-case⊎
    case⊎ L [inj₁ x ⇒ M |inj₂ y ⇒ N ] —→ case⊎ L′ [inj₁ x ⇒ M |inj₂ y ⇒ N ]

    --------------------------------------------------------- β-inj₁
    case⊎ (`inj₁ V) [inj₁ x ⇒ M |inj₂ y ⇒ N ] —→ M [ x := V ]

    --------------------------------------------------------- β-inj₂
    case⊎ (`inj₂ W) [inj₁ x ⇒ M |inj₂ y ⇒ N ] —→ N [ y := W ]

### Example

Here is a function to swap the components of a sum:

    swap⊎ : ∅ ⊢ A `⊎ B ⇒ B `⊎ A
    swap⊎ = ƛ z ⇒ case⊎ z
                    [inj₁ x ⇒ `inj₂ x
                    |inj₂ y ⇒ `inj₁ y ]


## Unit type

For the unit type, there is a way to introduce
values of the type but no way to eliminate values of the type.
There are no reduction rules.

### Syntax

    A, B, C ::= ...                     Types
      `⊤                                  unit type

    L, M, N ::= ...                     Terms
      `tt                                 unit value

    V, W ::= ...                        Values
      `tt                                 unit value

### Typing

    ------------ `tt or ⊤-I
    Γ ⊢ `tt ⦂ `⊤

### Reduction

(none)

### Example

Here is the isomorphism between `A` and ``A `× `⊤``:

    to×⊤ : ∅ ⊢ A ⇒ A `× `⊤
    to×⊤ = ƛ x ⇒ `⟨ x , `tt ⟩

    from×⊤ : ∅ ⊢ A `× `⊤ ⇒ A
    from×⊤ = ƛ z ⇒ `proj₁ z


## Alternative formulation of unit type

There is an alternative formulation of the unit type, where in place of
no way to eliminate the type we have a case term that binds zero variables.
We repeat the syntax in full, but only give the new type and reduction rules:

### Syntax

    A, B, C ::= ...                     Types
      `⊤                                  unit type

    L, M, N ::= ...                     Terms
      `tt                                 unit value
      `case⊤ L [tt⇒ N ]                   case

    V, W ::= ...                        Values
      `tt                                 unit value

### Typing

    Γ ⊢ L ⦂ `⊤
    Γ ⊢ M ⦂ A
    ------------------------ case⊤ or ⊤-E
    Γ ⊢ case⊤ L [tt⇒ M ] ⦂ A

### Reduction

    L —→ L′
    ------------------------------------- ξ-case⊤
    case⊤ L [tt⇒ M ] —→ case⊤ L′ [tt⇒ M ]

    ----------------------- β-case⊤
    case⊤ `tt [tt⇒ M ] —→ M

### Example

Here is half the isomorphism between `A` and ``A `× `⊤`` rewritten in the new notation:

    from×⊤-case : ∅ ⊢ A `× `⊤ ⇒ A
    from×⊤-case = ƛ z ⇒ case× z
                          [⟨ x , y ⟩⇒ case⊤ y
                                        [tt⇒ x ] ]


### Translation

We can translate the alternative formulation into one without case:

    (case⊤ L [tt⇒ M ]) †  =  `let z `= (L †) `in (M †)

Here `z` is a variable that does not appear free in `M`.


## Empty type

For the empty type, there is a way to eliminate values of
the type but no way to introduce values of the type.  There are no
values of the type and no β rule, but there is a ξ rule.  The `case⊥`
construct plays a role similar to `⊥-elim` in Agda:

### Syntax

    A, B, C ::= ...                     Types
      `⊥                                  empty type

    L, M, N ::= ...                     Terms
      case⊥ L []                          case

### Typing

    Γ ⊢ L ⦂ `⊥
    ------------------ case⊥ or ⊥-E
    Γ ⊢ case⊥ L [] ⦂ A

### Reduction

    L —→ L′
    ------------------------- ξ-case⊥
    case⊥ L [] —→ case⊥ L′ []

### Example

Here is the isomorphism between `A` and ``A `⊎ `⊥``:

    to⊎⊥ : ∅ ⊢ A ⇒ A `⊎ `⊥
    to⊎⊥ = ƛ x ⇒ `inj₁ x

    from⊎⊥ : ∅ ⊢ A `⊎ `⊥ ⇒ A
    from⊎⊥ = ƛ z ⇒ case⊎ z
                     [inj₁ x ⇒ x
                     |inj₂ y ⇒ case⊥ y
                                 [] ]

## Lists

### Syntax

    A, B, C ::= ...                     Types
      `List A                             list type

    L, M, N ::= ...                     Terms
      `[]                                 nil
      M `∷ N                              cons
      caseL L [[]⇒ M | x ∷ y ⇒ N ]        case

    V, W ::= ...                        Values
      `[]                                 nil
      V `∷ W                              cons

### Typing

    ----------------- `[] or List-I₁
    Γ ⊢ `[] ⦂ `List A

    Γ ⊢ M ⦂ A
    Γ ⊢ N ⦂ `List A
    -------------------- _`∷_ or List-I₂
    Γ ⊢ M `∷ N ⦂ `List A

    Γ ⊢ L ⦂ `List A
    Γ ⊢ M ⦂ B
    Γ , x ⦂ A , xs ⦂ `List A ⊢ N ⦂ B
    -------------------------------------- caseL or List-E
    Γ ⊢ caseL L [[]⇒ M | x ∷ xs ⇒ N ] ⦂ B

### Reduction

    M —→ M′
    ----------------- ξ-∷₁
    M `∷ N —→ M′ `∷ N

    N —→ N′
    ----------------- ξ-∷₂
    V `∷ N —→ V `∷ N′

    L —→ L′
    --------------------------------------------------------------- ξ-caseL
    caseL L [[]⇒ M | x ∷ xs ⇒ N ] —→ caseL L′ [[]⇒ M | x ∷ xs ⇒ N ]

    ------------------------------------ β-[]
    caseL `[] [[]⇒ M | x ∷ xs ⇒ N ] —→ M

    --------------------------------------------------------------- β-∷
    caseL (V `∷ W) [[]⇒ M | x ∷ xs ⇒ N ] —→ N [ x := V ][ xs := W ]

### Example

Here is the map function for lists:

    mapL : ∅ ⊢ (A ⇒ B) ⇒ `List A ⇒ `List B
    mapL = μ mL ⇒ ƛ f ⇒ ƛ xs ⇒
             caseL xs
               [[]⇒ `[]
               | x ∷ xs ⇒ f · x `∷ mL · f · xs ]


## Formalisation

We now show how to formalise

  * primitive numbers
  * _let_ bindings
  * products
  * an alternative formulation of products

and leave formalisation of the remaining constructs as an exercise.


### Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
```


### Syntax

```agda
infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_
infixr 9 _`×_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infixl 8 _`*_
infix  8 `suc_
infix  9 `_
infix  9 S_
infix  9 #_
```

### Types

```agda
data Type : Set where
  `ℕ    : Type
  _⇒_   : Type → Type → Type
  Nat   : Type
  _`×_  : Type → Type → Type
  -- begin
  _`⊎_ : Type → Type → Type
  `⊤ : Type
  `⊥ : Type
  `List : Type → Type
  -- end
```

### Contexts

```agda
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context
```

### Variables and the lookup judgment

```agda
data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ B
      ---------
    → Γ , A ∋ B
```

### Terms and the typing judgment

```agda
data _⊢_ : Context → Type → Set where

  -- variables

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  -- functions

  ƛ_  :  ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  -- naturals

  `zero : ∀ {Γ}
      ------
    → Γ ⊢ `ℕ

  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
      ------
    → Γ ⊢ `ℕ

  case : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , `ℕ ⊢ A
      -----
    → Γ ⊢ A

  -- fixpoint

  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
      ----------
    → Γ ⊢ A

  -- primitive numbers

  con : ∀ {Γ}
    → ℕ
      -------
    → Γ ⊢ Nat

  _`*_ : ∀ {Γ}
    → Γ ⊢ Nat
    → Γ ⊢ Nat
      -------
    → Γ ⊢ Nat

  -- let

  `let : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ , A ⊢ B
      ----------
    → Γ ⊢ B

  -- products

  `⟨_,_⟩ : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ ⊢ B
      -----------
    → Γ ⊢ A `× B

  `proj₁ : ∀ {Γ A B}
    → Γ ⊢ A `× B
      -----------
    → Γ ⊢ A

  `proj₂ : ∀ {Γ A B}
    → Γ ⊢ A `× B
      -----------
    → Γ ⊢ B

  -- alternative formulation of products

  case× : ∀ {Γ A B C}
    → Γ ⊢ A `× B
    → Γ , A , B ⊢ C
      --------------
    → Γ ⊢ C

  -- begin

  -- sums

  `inj₁ : ∀ {Γ A B}
    → Γ ⊢ A
      -----------
    → Γ ⊢ A `⊎ B

  `inj₂ : ∀ {Γ A B}
    → Γ ⊢ B
      -----------
    → Γ ⊢ A `⊎ B

  case⊎ : ∀ {Γ A B C}
    → Γ ⊢ A `⊎ B
    → Γ , A ⊢ C
    → Γ , B ⊢ C
      -----------
    → Γ ⊢ C

  -- unit

  `tt : ∀ {Γ}
      -------
    → Γ ⊢ `⊤
  
  -- alternative formulation of unit

  case⊤ : ∀ {Γ A}
    → Γ ⊢ `⊤
    → Γ ⊢ A
      -------
    → Γ ⊢ A

  -- empty

  case⊥ : ∀ {Γ A}
    → Γ ⊢ `⊥
      -------
    → Γ ⊢ A

  -- lists

  `[] : ∀ {Γ A}
      ------------
    → Γ ⊢ `List A

  _`∷_ : ∀ {Γ A}
    → Γ ⊢ A
    → Γ ⊢ `List A
      ------------
    → Γ ⊢ `List A

  caseL : ∀ {Γ A B}
    → Γ ⊢ `List A
    → Γ ⊢ B
    → Γ , A , `List A ⊢ B
      --------------------
    → Γ ⊢ B

  -- end
```

### Abbreviating de Bruijn indices

```agda
length : Context → ℕ
length ∅        =  zero
length (Γ , _)  =  suc (length Γ)

lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
lookup {(_ , A)} {zero}    (s≤s z≤n)  =  A
lookup {(Γ , _)} {(suc n)} (s≤s p)    =  lookup p

count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
count {_ , _} {zero}    (s≤s z≤n)  =  Z
count {Γ , _} {(suc n)} (s≤s p)    =  S (count p)

#_ : ∀ {Γ}
  → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
    --------------------------------
  → Γ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ}  =  ` count (toWitness n∈Γ)
```

## Renaming

```agda
ext : ∀ {Γ Δ}
  → (∀ {A}   →     Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B} → Γ , A ∋ B → Δ , A ∋ B)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (`zero)        =  `zero
rename ρ (`suc M)       =  `suc (rename ρ M)
rename ρ (case L M N)   =  case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (μ N)          =  μ (rename (ext ρ) N)
rename ρ (con n)        =  con n
rename ρ (M `* N)       =  rename ρ M `* rename ρ N
rename ρ (`let M N)     =  `let (rename ρ M) (rename (ext ρ) N)
rename ρ `⟨ M , N ⟩     =  `⟨ rename ρ M , rename ρ N ⟩
rename ρ (`proj₁ L)     =  `proj₁ (rename ρ L)
rename ρ (`proj₂ L)     =  `proj₂ (rename ρ L)
rename ρ (case× L M)    =  case× (rename ρ L) (rename (ext (ext ρ)) M)
-- begin
rename ρ (`inj₁ L) = `inj₁ (rename ρ L)
rename ρ (`inj₂ L) = `inj₂ (rename ρ L)
rename ρ (case⊎ L M N) = case⊎ (rename ρ L) (rename (ext ρ) M) (rename (ext ρ) N)
rename ρ `tt = `tt
rename ρ (case⊤ L M) = case⊤ (rename ρ L) (rename ρ M)
rename ρ (case⊥ L) = case⊥ (rename ρ L)
rename ρ `[] = `[]
rename ρ (L `∷ M) = rename ρ L `∷ rename ρ M
rename ρ (caseL L M N) = caseL (rename ρ L) (rename ρ M) (rename (ext (ext ρ)) N)
-- end
```

## Simultaneous Substitution

```agda
exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A) → (∀ {A B} → Γ , A ∋ B → Δ , A ⊢ B)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

subst : ∀ {Γ Δ} → (∀ {C} → Γ ∋ C → Δ ⊢ C) → (∀ {C} → Γ ⊢ C → Δ ⊢ C)
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
subst σ (`zero)        =  `zero
subst σ (`suc M)       =  `suc (subst σ M)
subst σ (case L M N)   =  case (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (μ N)          =  μ (subst (exts σ) N)
subst σ (con n)        =  con n
subst σ (M `* N)       =  subst σ M `* subst σ N
subst σ (`let M N)     =  `let (subst σ M) (subst (exts σ) N)
subst σ `⟨ M , N ⟩     =  `⟨ subst σ M , subst σ N ⟩
subst σ (`proj₁ L)     =  `proj₁ (subst σ L)
subst σ (`proj₂ L)     =  `proj₂ (subst σ L)
subst σ (case× L M)    =  case× (subst σ L) (subst (exts (exts σ)) M)
-- begin
subst σ (`inj₁ L) = `inj₁ (subst σ L)
subst σ (`inj₂ L) = `inj₂ (subst σ L)
subst σ (case⊎ L M N) = case⊎ (subst σ L) (subst (exts σ) M) (subst (exts σ) N)
subst σ `tt = `tt
subst σ (case⊤ L M) = case⊤ (subst σ L) (subst σ M)
subst σ (case⊥ L) = case⊥ (subst σ L)
subst σ `[] = `[]
subst σ (L `∷ M) = subst σ L `∷ subst σ M
subst σ (caseL L M N) = caseL (subst σ L) (subst σ M) (subst (exts (exts σ)) N)
-- end
```

## Single and double substitution

```agda
substZero : ∀ {Γ}{A B} → Γ ⊢ A → Γ , A ∋ B → Γ ⊢ B
substZero V Z      =  V
substZero V (S x)  =  ` x

_[_] : ∀ {Γ A B}
  → Γ , A ⊢ B
  → Γ ⊢ A
    ---------
  → Γ ⊢ B
_[_] {Γ} {A} N V =  subst {Γ , A} {Γ} (substZero V) N

_[_][_] : ∀ {Γ A B C}
  → Γ , A , B ⊢ C
  → Γ ⊢ A
  → Γ ⊢ B
    -------------
  → Γ ⊢ C
_[_][_] {Γ} {A} {B} N V W =  subst {Γ , A , B} {Γ} σ N
  where
  σ : ∀ {C} → Γ , A , B ∋ C → Γ ⊢ C
  σ Z          =  W
  σ (S Z)      =  V
  σ (S (S x))  =  ` x
```

## Values

```agda
data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  -- functions

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  -- naturals

  V-zero : ∀ {Γ}
      -----------------
    → Value (`zero {Γ})

  V-suc_ : ∀ {Γ} {V : Γ ⊢ `ℕ}
    → Value V
      --------------
    → Value (`suc V)

  -- primitives

  V-con : ∀ {Γ n}
      -----------------
    → Value (con {Γ} n)

  -- products

  V-⟨_,_⟩ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ----------------
    → Value `⟨ V , W ⟩

  -- begin

  -- sums

  V-inj₁ : ∀ {Γ A B} {V : Γ ⊢ A}
    → Value V
      ----------------------------
    → Value (`inj₁ {Γ} {A} {B} V)

  V-inj₂ : ∀ {Γ A B} {V : Γ ⊢ B}
    → Value V
      ----------------------------
    → Value (`inj₂ {Γ} {A} {B} V)

  -- unit

  V-tt : ∀ {Γ}
      ----------------
    → Value (`tt {Γ})

  -- empty

  -- lists

  V-[] : ∀ {Γ A}
    → Value (`[] {Γ} {A})

  V-∷ : ∀ {Γ A} {V : Γ ⊢ A} {W : Γ ⊢ `List A}
    → Value V
    → Value W
      ---------------
    → Value (V `∷ W)
    
  -- end
```

Implicit arguments need to be supplied when they are
not fixed by the given arguments.

## Reduction

```agda
infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  -- functions

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {V : Γ ⊢ A}
    → Value V
      --------------------
    → (ƛ N) · V —→ N [ V ]

  -- naturals

  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M —→ M′
      -----------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → L —→ L′
      -------------------------
    → case L M N —→ case L′ M N

  β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
      -------------------
    → case `zero M N —→ M

  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → Value V
      ----------------------------
    → case (`suc V) M N —→ N [ V ]

  -- fixpoint

  β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
      ----------------
    → μ N —→ N [ μ N ]

  -- primitive numbers

  ξ-*₁ : ∀ {Γ} {L L′ M : Γ ⊢ Nat}
    → L —→ L′
      -----------------
    → L `* M —→ L′ `* M

  ξ-*₂ : ∀ {Γ} {V M M′ : Γ ⊢ Nat}
    → Value V
    → M —→ M′
      -----------------
    → V `* M —→ V `* M′

  δ-* : ∀ {Γ c d}
      ---------------------------------
    → con {Γ} c `* con d —→ con (c * d)

  -- let

  ξ-let : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ , A ⊢ B}
    → M —→ M′
      ---------------------
    → `let M N —→ `let M′ N

  β-let : ∀ {Γ A B} {V : Γ ⊢ A} {N : Γ , A ⊢ B}
    → Value V
      -------------------
    → `let V N —→ N [ V ]

  -- products

  ξ-⟨,⟩₁ : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ ⊢ B}
    → M —→ M′
      -------------------------
    → `⟨ M , N ⟩ —→ `⟨ M′ , N ⟩

  ξ-⟨,⟩₂ : ∀ {Γ A B} {V : Γ ⊢ A} {N N′ : Γ ⊢ B}
    → Value V
    → N —→ N′
      -------------------------
    → `⟨ V , N ⟩ —→ `⟨ V , N′ ⟩

  ξ-proj₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A `× B}
    → L —→ L′
      ---------------------
    → `proj₁ L —→ `proj₁ L′

  ξ-proj₂ : ∀ {Γ A B} {L L′ : Γ ⊢ A `× B}
    → L —→ L′
      ---------------------
    → `proj₂ L —→ `proj₂ L′

  β-proj₁ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ----------------------
    → `proj₁ `⟨ V , W ⟩ —→ V

  β-proj₂ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ----------------------
    → `proj₂ `⟨ V , W ⟩ —→ W

  -- alternative formulation of products

  ξ-case× : ∀ {Γ A B C} {L L′ : Γ ⊢ A `× B} {M : Γ , A , B ⊢ C}
    → L —→ L′
      -----------------------
    → case× L M —→ case× L′ M

  β-case× : ∀ {Γ A B C} {V : Γ ⊢ A} {W : Γ ⊢ B} {M : Γ , A , B ⊢ C}
    → Value V
    → Value W
      ----------------------------------
    → case× `⟨ V , W ⟩ M —→ M [ V ][ W ]

  -- begin

  -- sum

  ξ-inj₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A}
    → L —→ L′
      --------------------------------
    → `inj₁ {Γ} {A} {B} L —→ `inj₁ L′

  ξ-inj₂ : ∀ {Γ A B} {L L′ : Γ ⊢ B}
    → L —→ L′
      --------------------------------
    → `inj₂ {Γ} {A} {B} L —→ `inj₂ L′

  ξ-case⊎ : ∀ {Γ A B C} {L L′ : Γ ⊢ A `⊎ B} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
    → L —→ L′
      ----------------------------
    → case⊎ L M N —→ case⊎ L′ M N

  β-inj₁ : ∀ {Γ A B C} {V : Γ ⊢ A} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
    → Value V
      -------------------------------
    → case⊎ (`inj₁ V) M N —→ M [ V ]

  β-inj₂ : ∀ {Γ A B C} {V : Γ ⊢ B} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
    → Value V
      -------------------------------
    → case⊎ (`inj₂ V) M N —→ N [ V ]

  -- unit

  -- alternative formulation of unit

  ξ-case⊤ : ∀ {Γ A} {L L′ : Γ ⊢ `⊤} {M : Γ ⊢ A}
    → L —→ L′
      ------------------------
    → case⊤ L M —→ case⊤ L′ M

  β-case⊤ : ∀ {Γ A} {M : Γ ⊢ A}
      -----------------
    → case⊤ `tt M —→ M

  -- empty

  ξ-case⊥ : ∀ {Γ A} {L L′ : Γ ⊢ `⊥}
    → L —→ L′
      ---------------------
    → case⊥ {Γ} {A} L —→ case⊥ L′
  
  -- lists

  ξ-∷₁ : ∀ {Γ A} {L L′ : Γ ⊢ A} {M : Γ ⊢ `List A}
    → L —→ L′
      ------------------
    → L `∷ M —→ L′ `∷ M

  ξ-∷₂ : ∀ {Γ A} {V : Γ ⊢ A} {M M′ : Γ ⊢ `List A}
    → Value V
    → M —→ M′
      ------------------
    → V `∷ M —→ V `∷ M′

  ξ-caseL : ∀ {Γ A B} {L L′ : Γ ⊢ `List A} {M : Γ ⊢ B} {N : Γ , A , `List A ⊢ B}
    → L —→ L′
      ----------------------------
    → caseL L M N —→ caseL L′ M N

  β-[] : ∀ {Γ A B} {M : Γ ⊢ B} {N : Γ , A , `List A ⊢ B}
      -------------------
    → caseL `[] M N —→ M

  β-∷ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ `List A} {M : Γ ⊢ B} {N : Γ , A , `List A ⊢ B}
    → Value V
    → Value W
      ------------------------------------
    → caseL (V `∷ W) M N —→ N [ V ][ W ]

  -- end
```

## Reflexive and transitive closure

```agda
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : (M : Γ ⊢ A)
      ------
    → M —↠ M

  _—→⟨_⟩_ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ------
    → L —↠ N

begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N
```


## Values do not reduce

```agda
V¬—→ : ∀ {Γ A} {M N : Γ ⊢ A}
  → Value M
    ----------
  → ¬ (M —→ N)
V¬—→ V-ƛ          ()
V¬—→ V-zero       ()
V¬—→ (V-suc VM)   (ξ-suc M—→M′)     =  V¬—→ VM M—→M′
V¬—→ V-con        ()
V¬—→ V-⟨ VM , _ ⟩ (ξ-⟨,⟩₁ M—→M′)    =  V¬—→ VM M—→M′
V¬—→ V-⟨ _ , VN ⟩ (ξ-⟨,⟩₂ _ N—→N′)  =  V¬—→ VN N—→N′
-- begin
V¬—→ (V-inj₁ VM) (ξ-inj₁ M—→M′) = V¬—→ VM M—→M′
V¬—→ (V-inj₂ VN) (ξ-inj₂ N—→N′) = V¬—→ VN N—→N′
V¬—→ (V-∷ VM _) (ξ-∷₁ M—→M′) = V¬—→ VM M—→M′
V¬—→ (V-∷ _ VN) (ξ-∷₂ _ N—→N′) = V¬—→ VN N—→N′
-- end
```


## Progress

```agda
data Progress {A} (M : ∅ ⊢ A) : Set where

  step : ∀ {N : ∅ ⊢ A}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {A}
  → (M : ∅ ⊢ A)
    -----------
  → Progress M
progress (` ())
progress (ƛ N)                              =  done V-ƛ
progress (L · M) with progress L
...    | step L—→L′                         =  step (ξ-·₁ L—→L′)
...    | done V-ƛ with progress M
...        | step M—→M′                     =  step (ξ-·₂ V-ƛ M—→M′)
...        | done VM                        =  step (β-ƛ VM)
progress (`zero)                            =  done V-zero
progress (`suc M) with progress M
...    | step M—→M′                         =  step (ξ-suc M—→M′)
...    | done VM                            =  done (V-suc VM)
progress (case L M N) with progress L
...    | step L—→L′                         =  step (ξ-case L—→L′)
...    | done V-zero                        =  step β-zero
...    | done (V-suc VL)                    =  step (β-suc VL)
progress (μ N)                              =  step β-μ
progress (con n)                            =  done V-con
progress (L `* M) with progress L
...    | step L—→L′                         =  step (ξ-*₁ L—→L′)
...    | done V-con with progress M
...        | step M—→M′                     =  step (ξ-*₂ V-con M—→M′)
...        | done V-con                     =  step δ-*
progress (`let M N) with progress M
...    | step M—→M′                         =  step (ξ-let M—→M′)
...    | done VM                            =  step (β-let VM)
progress `⟨ M , N ⟩ with progress M
...    | step M—→M′                         =  step (ξ-⟨,⟩₁ M—→M′)
...    | done VM with progress N
...        | step N—→N′                     =  step (ξ-⟨,⟩₂ VM N—→N′)
...        | done VN                        =  done (V-⟨ VM , VN ⟩)
progress (`proj₁ L) with progress L
...    | step L—→L′                         =  step (ξ-proj₁ L—→L′)
...    | done (V-⟨ VM , VN ⟩)               =  step (β-proj₁ VM VN)
progress (`proj₂ L) with progress L
...    | step L—→L′                         =  step (ξ-proj₂ L—→L′)
...    | done (V-⟨ VM , VN ⟩)               =  step (β-proj₂ VM VN)
progress (case× L M) with progress L
...    | step L—→L′                         =  step (ξ-case× L—→L′)
...    | done (V-⟨ VM , VN ⟩)               =  step (β-case× VM VN)
-- begin
progress (`inj₁ L) with progress L
... | step L—→L′ = step (ξ-inj₁ L—→L′)
... | done VL = done (V-inj₁ VL)
progress (`inj₂ L) with progress L
... | step L—→L′ = step (ξ-inj₂ L—→L′)
... | done VL = done (V-inj₂ VL)
progress (case⊎ L M N) with progress L
... | step L—→L′ = step (ξ-case⊎ L—→L′)
... | done (V-inj₁ VL) = step (β-inj₁ VL)
... | done (V-inj₂ VL) = step (β-inj₂ VL)
progress `tt = done (V-tt)
progress (case⊤ L M) with progress L
... | step L—→L′ = step (ξ-case⊤ L—→L′)
... | done V-tt = step β-case⊤
progress (case⊥ L) with progress L
... | step L—→L′ = step (ξ-case⊥ L—→L′)
... | done ()
progress `[] = done V-[]
progress (L `∷ M) with progress L
... | step L—→L′ = step (ξ-∷₁ L—→L′)
... | done VL with progress M
...   | step M—→M′ = step (ξ-∷₂ VL M—→M′)
...   | done VM = done (V-∷ VL VM)
progress (caseL L M N) with progress L
... | step L—→L′ = step (ξ-caseL L—→L′)
... | done V-[] = step β-[]
... | done (V-∷ VL VL′) = step (β-∷ VL VL′)
-- end
```


## Evaluation

```agda
record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished {Γ A} (N : Γ ⊢ A) : Set where

   done :
       Value N
       ----------
     → Finished N

   out-of-gas :
       ----------
       Finished N

data Steps {A} : ∅ ⊢ A → Set where

  steps : {L N : ∅ ⊢ A}
    → L —↠ N
    → Finished N
      ----------
    → Steps L

eval : ∀ {A}
  → Gas
  → (L : ∅ ⊢ A)
    -----------
  → Steps L
eval (gas zero)    L                     =  steps (L ∎) out-of-gas
eval (gas (suc m)) L with progress L
... | done VL                            =  steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) M
...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
```


## Examples

```agda
cube : ∅ ⊢ Nat ⇒ Nat
cube = ƛ (# 0 `* # 0 `* # 0)

_ : cube · con 2 —↠ con 8
_ =
  begin
    cube · con 2
  —→⟨ β-ƛ V-con ⟩
    con 2 `* con 2 `* con 2
  —→⟨ ξ-*₁ δ-* ⟩
    con 4 `* con 2
  —→⟨ δ-* ⟩
    con 8
  ∎

exp10 : ∅ ⊢ Nat ⇒ Nat
exp10 = ƛ (`let (# 0 `* # 0)
            (`let (# 0 `* # 0)
              (`let (# 0 `* # 2)
                (# 0 `* # 0))))

_ : exp10 · con 2 —↠ con 1024
_ =
  begin
    exp10 · con 2
  —→⟨ β-ƛ V-con ⟩
    `let (con 2 `* con 2) (`let (# 0 `* # 0) (`let (# 0 `* con 2) (# 0 `* # 0)))
  —→⟨ ξ-let δ-* ⟩
    `let (con 4) (`let (# 0 `* # 0) (`let (# 0 `* con 2) (# 0 `* # 0)))
  —→⟨ β-let V-con ⟩
    `let (con 4 `* con 4) (`let (# 0 `* con 2) (# 0 `* # 0))
  —→⟨ ξ-let δ-* ⟩
    `let (con 16) (`let (# 0 `* con 2) (# 0 `* # 0))
  —→⟨ β-let V-con ⟩
    `let (con 16 `* con 2) (# 0 `* # 0)
  —→⟨ ξ-let δ-* ⟩
    `let (con 32) (# 0 `* # 0)
  —→⟨ β-let V-con ⟩
    con 32 `* con 32
  —→⟨ δ-* ⟩
    con 1024
  ∎

swap× : ∀ {A B} → ∅ ⊢ A `× B ⇒ B `× A
swap× = ƛ `⟨ `proj₂ (# 0) , `proj₁ (# 0) ⟩

_ : swap× · `⟨ con 42 , `zero ⟩ —↠ `⟨ `zero , con 42 ⟩
_ =
  begin
    swap× · `⟨ con 42 , `zero ⟩
  —→⟨ β-ƛ V-⟨ V-con , V-zero ⟩ ⟩
    `⟨ `proj₂ `⟨ con 42 , `zero ⟩ , `proj₁ `⟨ con 42 , `zero ⟩ ⟩
  —→⟨ ξ-⟨,⟩₁ (β-proj₂ V-con V-zero) ⟩
    `⟨ `zero , `proj₁ `⟨ con 42 , `zero ⟩ ⟩
  —→⟨ ξ-⟨,⟩₂ V-zero (β-proj₁ V-con V-zero) ⟩
    `⟨ `zero , con 42 ⟩
  ∎

swap×-case : ∀ {A B} → ∅ ⊢ A `× B ⇒ B `× A
swap×-case = ƛ case× (# 0) `⟨ # 0 , # 1 ⟩

_ : swap×-case · `⟨ con 42 , `zero ⟩ —↠ `⟨ `zero , con 42 ⟩
_ =
  begin
     swap×-case · `⟨ con 42 , `zero ⟩
   —→⟨ β-ƛ V-⟨ V-con , V-zero ⟩ ⟩
     case× `⟨ con 42 , `zero ⟩ `⟨ # 0 , # 1 ⟩
   —→⟨ β-case× V-con V-zero ⟩
     `⟨ `zero , con 42 ⟩
   ∎
```

#### Exercise `More` (recommended and practice)

Formalise the remaining constructs defined in this chapter.
Make your changes in this file.
Evaluate each example, applied to data as needed,
to confirm it returns the expected answer:

  * sums (recommended)
  * unit type (practice)
  * an alternative formulation of unit type (practice)
  * empty type (recommended)
  * lists (practice)

Please delimit any code you add as follows:

    -- begin
    -- end


#### Exercise `double-subst` (stretch)

Show that a double substitution is equivalent to two single
substitutions.
```agda
--postulate
double-subst :
    ∀ {Γ A B C} {V : Γ ⊢ A} {W : Γ ⊢ B} {N : Γ , A , B ⊢ C} →
      N [ V ][ W ] ≡ (N [ rename S_ W ]) [ V ]
```
Note the arguments need to be swapped and `W` needs to have
its context adjusted via renaming in order for the right-hand
side to be well typed.

```agda
open Eq using (sym; cong)
open Eq.≡-Reasoning renaming (begin_ to ≡begin_; _∎ to _≡∎)

ext-ext : ∀ {Γ Δ Ε}
  → (σ : ∀ {A} → Γ ∋ A → Δ ∋ A)
  → (τ : ∀ {A} → Δ ∋ A → Ε ∋ A)
  → ∀ {A B} (x : Γ , A ∋ B)
  → ext τ (ext σ x) ≡ ext (λ v → τ (σ v)) x
ext-ext σ τ Z = refl
ext-ext σ τ (S x) = refl

ext-ext-ext-ext : ∀ {Γ Δ Ε}
  → (σ : ∀ {A} → Γ ∋ A → Δ ∋ A)
  → (τ : ∀ {A} → Δ ∋ A → Ε ∋ A)
  → ∀ {A B C} (x : Γ , A , B ∋ C)
  → ext (ext τ) (ext (ext σ) x) ≡ ext (ext (λ v → τ (σ v))) x
ext-ext-ext-ext σ τ Z = refl
ext-ext-ext-ext σ τ (S Z) = refl
ext-ext-ext-ext σ τ (S (S x)) = refl

cong-ext : ∀ {Γ Δ} {σ τ : ∀ {A} → Γ ∋ A → Δ ∋ A}
  → (σ~τ : ∀ {A} (x : Γ ∋ A) → σ x ≡ τ x)
  → ∀ {A B} (x : Γ , A ∋ B)
  → ext σ x ≡ ext τ x
cong-ext σ~τ Z = refl
cong-ext σ~τ (S x) = cong S_ (σ~τ x)

cong-rename : ∀ {Γ Δ} {σ τ : ∀ {A} → Γ ∋ A → Δ ∋ A}
  → (∀ {A} (x : Γ ∋ A) → σ x ≡ τ x)
  → ∀ {A} (L : Γ ⊢ A)
  → rename σ L ≡ rename τ L
cong-rename σ~τ (` x) = cong `_ (σ~τ x)
cong-rename σ~τ (ƛ L)
  rewrite cong-rename (cong-ext σ~τ) L = refl
cong-rename σ~τ (L · M)
  rewrite cong-rename σ~τ L | cong-rename σ~τ M = refl
cong-rename σ~τ `zero = refl
cong-rename σ~τ (`suc L)
  rewrite cong-rename σ~τ L = refl
cong-rename σ~τ (case L M N)
  rewrite cong-rename σ~τ L | cong-rename σ~τ M | cong-rename (cong-ext σ~τ) N = refl
cong-rename σ~τ (μ L)
  rewrite cong-rename (cong-ext σ~τ) L = refl
cong-rename σ~τ (con x) = refl
cong-rename σ~τ (L `* M)
  rewrite cong-rename σ~τ L | cong-rename σ~τ M = refl
cong-rename σ~τ (`let L M)
  rewrite cong-rename σ~τ L | cong-rename (cong-ext σ~τ) M = refl
cong-rename σ~τ `⟨ L , M ⟩
  rewrite cong-rename σ~τ L | cong-rename σ~τ M = refl
cong-rename σ~τ (`proj₁ L)
  rewrite cong-rename σ~τ L = refl
cong-rename σ~τ (`proj₂ L)
  rewrite cong-rename σ~τ L = refl
cong-rename σ~τ (case× L M)
  rewrite cong-rename σ~τ L | cong-rename (cong-ext (cong-ext σ~τ)) M = refl
cong-rename σ~τ (`inj₁ L)
  rewrite cong-rename σ~τ L = refl
cong-rename σ~τ (`inj₂ L)
  rewrite cong-rename σ~τ L = refl
cong-rename σ~τ (case⊎ L M N)
  rewrite cong-rename σ~τ L | cong-rename (cong-ext σ~τ) M | cong-rename (cong-ext σ~τ) N
  = refl
cong-rename σ~τ `tt = refl
cong-rename σ~τ (case⊤ L M)
  rewrite cong-rename σ~τ L | cong-rename σ~τ M = refl
cong-rename σ~τ (case⊥ L)
  rewrite cong-rename σ~τ L = refl
cong-rename σ~τ `[] = refl
cong-rename σ~τ (L `∷ M)
  rewrite cong-rename σ~τ L | cong-rename σ~τ M = refl
cong-rename σ~τ (caseL L M N)
  rewrite cong-rename σ~τ L | cong-rename σ~τ M | cong-rename (cong-ext (cong-ext σ~τ)) N
  = refl

rename-rename : ∀ {Γ Δ Ε}
  → (σ : ∀ {A} → Γ ∋ A → Δ ∋ A)
  → (τ : ∀ {A} → Δ ∋ A → Ε ∋ A)
  → ∀ {A} (L : Γ ⊢ A)
  → rename τ (rename σ L) ≡ rename (λ v → τ (σ v)) L
rename-rename σ τ (` x) = refl
rename-rename σ τ (ƛ L)
  rewrite rename-rename (ext σ) (ext τ) L | cong-rename (ext-ext σ τ) L = refl
rename-rename σ τ (L · M)
  rewrite rename-rename σ τ L | rename-rename σ τ M = refl
rename-rename σ τ `zero = refl
rename-rename σ τ (`suc L)
  rewrite rename-rename σ τ L = refl
rename-rename σ τ (case L M N)
  rewrite rename-rename σ τ L
  | rename-rename σ τ M
  | rename-rename (ext σ) (ext τ) N | cong-rename (ext-ext σ τ) N
  = refl
rename-rename σ τ (μ L)
  rewrite rename-rename (ext σ) (ext τ) L | cong-rename (ext-ext σ τ) L = refl
rename-rename σ τ (con x) = refl
rename-rename σ τ (L `* M)
  rewrite rename-rename σ τ L | rename-rename σ τ M = refl
rename-rename σ τ (`let L M)
  rewrite rename-rename σ τ L
  | rename-rename (ext σ) (ext τ) M | cong-rename (ext-ext σ τ) M
  = refl
rename-rename σ τ `⟨ L , M ⟩
  rewrite rename-rename σ τ L | rename-rename σ τ M = refl
rename-rename σ τ (`proj₁ L)
  rewrite rename-rename σ τ L = refl
rename-rename σ τ (`proj₂ L)
  rewrite rename-rename σ τ L = refl
rename-rename σ τ (case× L M)
  rewrite rename-rename σ τ L
  | rename-rename (ext (ext σ)) (ext (ext τ)) M
  | cong-rename (λ x → ext-ext-ext-ext σ τ x) M
  = refl
rename-rename σ τ (`inj₁ L)
  rewrite rename-rename σ τ L = refl
rename-rename σ τ (`inj₂ L)
  rewrite rename-rename σ τ L = refl
rename-rename σ τ (case⊎ L M N)
  rewrite rename-rename σ τ L
  | rename-rename (ext σ) (ext τ) M | cong-rename (ext-ext σ τ) M
  | rename-rename (ext σ) (ext τ) N | cong-rename (ext-ext σ τ) N
  = refl
rename-rename σ τ `tt = refl
rename-rename σ τ (case⊤ L M)
  rewrite rename-rename σ τ L | rename-rename σ τ M = refl
rename-rename σ τ (case⊥ L)
  rewrite rename-rename σ τ L = refl
rename-rename σ τ `[] = refl
rename-rename σ τ (L `∷ M)
  rewrite rename-rename σ τ L | rename-rename σ τ M = refl
rename-rename σ τ (caseL L M N)
  rewrite rename-rename σ τ L
  | rename-rename σ τ M
  | rename-rename (ext (ext σ)) (ext (ext τ)) N
  | cong-rename (ext-ext-ext-ext σ τ) N
  = refl

cong-exts : ∀ {Γ Δ} {σ τ : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} (x : Γ ∋ A) → σ x ≡ τ x)
  → ∀ {A B} (x : Γ , A ∋ B)
  → exts σ x ≡ exts τ x
cong-exts σ~τ Z = refl
cong-exts σ~τ (S x) = cong (rename S_) (σ~τ x)

cong-subst : ∀ {Γ Δ} {σ τ : ∀ {C} → Γ ∋ C → Δ ⊢ C}
  → (∀ {C} (x : Γ ∋ C) → σ x ≡ τ x)
  → ∀ {C} (L : Γ ⊢ C)
  → subst σ L ≡ subst τ L
cong-subst σ~τ (` x) = σ~τ x
cong-subst σ~τ (ƛ L)
  rewrite cong-subst (cong-exts σ~τ) L = refl
cong-subst σ~τ (L · M)
  rewrite cong-subst σ~τ L | cong-subst σ~τ M = refl
cong-subst σ~τ `zero = refl
cong-subst σ~τ (`suc L)
  rewrite cong-subst σ~τ L = refl
cong-subst σ~τ (case L M N)
  rewrite cong-subst σ~τ L | cong-subst σ~τ M | cong-subst (cong-exts σ~τ) N = refl
cong-subst σ~τ (μ L)
  rewrite cong-subst (cong-exts σ~τ) L = refl
cong-subst σ~τ (con x) = refl
cong-subst σ~τ (L `* M)
  rewrite cong-subst σ~τ L | cong-subst σ~τ M = refl
cong-subst σ~τ (`let L M)
  rewrite cong-subst σ~τ L | cong-subst (cong-exts σ~τ) M = refl
cong-subst σ~τ `⟨ L , M ⟩
  rewrite cong-subst σ~τ L | cong-subst σ~τ M = refl
cong-subst σ~τ (`proj₁ L)
  rewrite cong-subst σ~τ L = refl
cong-subst σ~τ (`proj₂ L)
  rewrite cong-subst σ~τ L = refl
cong-subst σ~τ (case× L M)
  rewrite cong-subst σ~τ L | cong-subst (cong-exts (cong-exts σ~τ)) M = refl
cong-subst σ~τ (`inj₁ L)
  rewrite cong-subst σ~τ L = refl
cong-subst σ~τ (`inj₂ L)
  rewrite cong-subst σ~τ L = refl
cong-subst σ~τ (case⊎ L M N)
  rewrite cong-subst σ~τ L | cong-subst (cong-exts σ~τ) M | cong-subst (cong-exts σ~τ) N
  = refl
cong-subst σ~τ `tt = refl
cong-subst σ~τ (case⊤ L M)
  rewrite cong-subst σ~τ L | cong-subst σ~τ M = refl
cong-subst σ~τ (case⊥ L)
  rewrite cong-subst σ~τ L = refl
cong-subst σ~τ `[] = refl
cong-subst σ~τ (L `∷ M)
  rewrite cong-subst σ~τ L | cong-subst σ~τ M = refl
cong-subst σ~τ (caseL L M N)
  rewrite cong-subst σ~τ L | cong-subst σ~τ M | cong-subst (cong-exts (cong-exts σ~τ)) N
  = refl

subst01 : ∀ {Γ A B C} → Γ ⊢ A → Γ ⊢ B → Γ , A , B ∋ C → Γ ⊢ C
subst01 V W Z = W
subst01 V W (S Z) = V
subst01 V W (S (S x)) = ` x

_++_ : Context → Context → Context
Γ ++ ∅ = Γ
Γ ++ (Δ , x) = Γ ++ Δ , x

weak : ∀ {Γ A} (Δ : Context) {B} → Γ ++ Δ ∋ A → (Γ , B) ++ Δ ∋ A
weak ∅ x = S x
weak (Δ , y) Z = Z
weak (Δ , y) (S x) = S (weak Δ x)

extss : ∀ {Γ Δ} (Γ′ : Context) → (∀ {A} → Γ ∋ A → Δ ⊢ A)
  → ∀ {B}
  → Γ ++ Γ′ ∋ B
  → Δ ++ Γ′ ⊢ B
extss ∅ σ x = σ x
extss (Γ′ , y) σ Z = ` Z
extss (Γ′ , y) σ (S x) = rename S_ (extss Γ′ σ x)

_ : ∀ {Γ A B} (x : Γ ∋ A) → weak ∅ {B} x ≡ S x
_ = λ x → refl

_ : ∀ {Γ A B C} (x : Γ , C ∋ A) → weak (∅ , C) {B} x ≡ ext S_ x
_ = λ { Z → refl ; (S x) → refl }

_ : ∀ {Γ A B C D} (x : Γ , C , D ∋ A) → weak (∅ , C , D) {B} x ≡ ext (ext S_) x
_ = λ { Z → refl ; (S Z) → refl ; (S (S x)) → refl }

_ : ∀ {Γ Δ A} (σ : ∀ {C} → Γ ∋ C → Δ ⊢ C) (x : Γ ∋ A) → extss ∅ σ x ≡ σ x
_ = λ σ x → refl

_ : ∀ {Γ Δ A B} (σ : ∀ {C} → Γ ∋ C → Δ ⊢ C) (x : Γ , B ∋ A) → extss (∅ , B) σ x ≡ exts σ x
_ = λ σ → λ { Z → refl ; (S x) → refl }

exts-extss : ∀ {Γ Δ A B} (Γ′ : Context) (σ : ∀ {A} → Γ ∋ A → Δ ⊢ A) (x : Γ ++ Γ′ , B ∋ A)
  → exts (extss Γ′ σ) x ≡ extss (Γ′ , B) σ x
exts-extss Γ′ σ Z = refl
exts-extss Γ′ σ (S x) = refl

ext-weak : ∀ {Γ A B} (Δ : Context) {C} (x : Γ ++ Δ , B ∋ A)
  → ext (weak Δ {C}) x ≡ weak (Δ , B) {C} x
ext-weak ∅ Z = refl
ext-weak ∅ (S x) = refl
ext-weak (Δ , y) Z = refl
ext-weak (Δ , y) (S x) = refl

extss-substZero-weak : ∀ {Γ A B} (Δ : Context) (V : Γ ⊢ A) (x : Γ ++ Δ ∋ B)
  → extss Δ (substZero V) (weak Δ x) ≡ ` x
extss-substZero-weak ∅ V x = refl
extss-substZero-weak (Δ , D) V Z = refl
extss-substZero-weak (Δ , D) V (S x)
  rewrite extss-substZero-weak Δ V x = refl

rename-weak-extss≡extss-exts-weak : ∀ {Γ Γ′} (σ : ∀ {A} → Γ ∋ A → Γ′ ⊢ A) (B : Type)
  → ∀ (Δ : Context) {A} (x : Γ ++ Δ ∋ A)
  → rename (weak Δ {B}) (extss Δ σ x) ≡ extss Δ (exts σ) (weak Δ x)
rename-weak-extss≡extss-exts-weak σ B ∅ x = refl
rename-weak-extss≡extss-exts-weak σ B (Δ , D) Z = refl
rename-weak-extss≡extss-exts-weak σ B (Δ , D) (S x) =
  ≡begin
    rename (weak (Δ , D)) (rename S_ (extss Δ σ x))
  ≡⟨ sym (cong-rename (ext-weak Δ) (rename S_ (extss Δ σ x))) ⟩
    rename (ext (weak Δ)) (rename S_ (extss Δ σ x))
  ≡⟨ rename-rename S_ (ext (weak Δ)) (extss Δ σ x) ⟩
    rename (λ x → ext (weak Δ) (S x)) (extss Δ σ x)
  ≡⟨ cong-rename (λ x → refl) (extss Δ σ x) ⟩
    rename (λ x → S (weak Δ x)) (extss Δ σ x)
  ≡⟨ sym (rename-rename (weak Δ) S_ (extss Δ σ x)) ⟩
    rename S_ (rename (weak Δ) (extss Δ σ x))
  ≡⟨ cong (rename S_) (rename-weak-extss≡extss-exts-weak σ B Δ x) ⟩
    rename S_ (extss Δ (exts σ) (weak Δ x))
  ≡∎

{-
-- Dependency Tree --

- double-subst
  - ds
    - ds1a
    - ds1b
    - ds2a
    - ds2b
    - dsv
      - dsvZ
        - dsvZ1
        - dsvZ2
      - dsvh
        - dsvh1a
        - dsvh1b
        - dsvh2a
        - dsvh2b
-}

dsvZ1 : ∀ {Γ A B} (Δ : Context) {C} (V : Γ ⊢ A) (W : Γ ++ Δ , C ⊢ B)
  → subst (exts (extss Δ (substZero V))) (rename (ext (weak Δ)) W)
    ≡ subst (extss (Δ , C) (substZero V)) (rename (weak (Δ , C)) W)
dsvZ1 Δ {C} V W
  rewrite cong-subst (exts-extss Δ (substZero V)) (rename (ext (weak Δ)) W)
  | cong (subst (extss (Δ , C) (substZero V))) (cong-rename (ext-weak Δ) W)
  = refl

dsvZ2 : ∀ {Γ A B} (Δ : Context) {C D} (V : Γ ⊢ A) (W : Γ ++ Δ , C , D ⊢ B)
  → subst (exts (exts (extss Δ (substZero V)))) (rename (ext (ext (weak Δ))) W)
    ≡ subst (extss (Δ , C , D) (substZero V)) (rename (weak (Δ , C , D)) W)
dsvZ2 Δ {C} {D} V W =
  ≡begin
    subst (exts (exts (extss Δ _))) (rename (ext (ext (weak Δ))) W)
  ≡⟨ cong (subst _) (cong-rename (cong-ext (ext-weak Δ)) W) ⟩
    subst (exts (exts (extss Δ _))) (rename (ext (weak (Δ , C))) W)
  ≡⟨ cong (subst _) (cong-rename (ext-weak (Δ , C)) W) ⟩
    subst (exts (exts (extss Δ _))) (rename (weak (Δ , C , D)) W)
  ≡⟨ cong-subst (cong-exts (exts-extss Δ _)) (rename (weak (Δ , C , D)) W)  ⟩
    subst (exts (extss (Δ , C) _)) (rename (weak (Δ , C , D)) W)
  ≡⟨ cong-subst (exts-extss (Δ , C) _) (rename (weak (Δ , C , D)) W) ⟩
    subst (extss (Δ , C , D) (substZero V)) (rename (weak (Δ , C , D)) W)
  ≡∎

dsvZ : ∀ {Γ A B} (Δ : Context) (V : Γ ⊢ A) (W : Γ ++ Δ ⊢ B)
  → subst (extss Δ (substZero V)) (rename (weak Δ) W) ≡ W
dsvZ Δ V (` x) = extss-substZero-weak Δ V x
dsvZ Δ V (ƛ W)
  rewrite dsvZ1 Δ V W | dsvZ (Δ , _) V W = refl
dsvZ Δ V (M · N)
  rewrite dsvZ Δ V M | dsvZ Δ V N = refl
dsvZ Δ V `zero = refl
dsvZ Δ V (`suc W)
  rewrite dsvZ Δ V W = refl
dsvZ Δ V (case L M N)
  rewrite dsvZ Δ V L | dsvZ Δ V M | dsvZ1 Δ V N | dsvZ (Δ , _) V N = refl
dsvZ Δ V (μ W)
  rewrite dsvZ1 Δ V W | dsvZ (Δ , _) V W = refl
dsvZ Δ V (con x) = refl
dsvZ Δ V (M `* N)
  rewrite dsvZ Δ V M | dsvZ Δ V N = refl
dsvZ Δ V (`let M N)
  rewrite dsvZ Δ V M | dsvZ1 Δ V N | dsvZ (Δ , _) V N = refl
dsvZ Δ V `⟨ M , N ⟩
  rewrite dsvZ Δ V M | dsvZ Δ V N = refl
dsvZ Δ V (`proj₁ W)
  rewrite dsvZ Δ V W = refl
dsvZ Δ V (`proj₂ W)
  rewrite dsvZ Δ V W = refl
dsvZ Δ V (case× M N)
  rewrite dsvZ Δ V M | dsvZ2 Δ V N | dsvZ (Δ , _ , _) V N = refl
dsvZ Δ V (`inj₁ W)
  rewrite dsvZ Δ V W = refl
dsvZ Δ V (`inj₂ W)
  rewrite dsvZ Δ V W = refl
dsvZ Δ V (case⊎ L M N)
  rewrite dsvZ Δ V L | dsvZ1 Δ V M | dsvZ (Δ , _) V M | dsvZ1 Δ V N | dsvZ (Δ , _) V N = refl
dsvZ Δ V `tt = refl
dsvZ Δ V (case⊤ M N)
  rewrite dsvZ Δ V M | dsvZ Δ V N = refl
dsvZ Δ V (case⊥ W)
  rewrite dsvZ Δ V W = refl
dsvZ Δ V `[] = refl
dsvZ Δ V (M `∷ N)
  rewrite dsvZ Δ V M | dsvZ Δ V N = refl
dsvZ Δ V (caseL L M N)
  rewrite dsvZ Δ V L | dsvZ Δ V M | dsvZ2 Δ V N | dsvZ (Δ , _ , _) V N = refl

dsvh1a : ∀ {Γ Γ′} (σ : ∀ {A} → Γ ∋ A → Γ′ ⊢ A) (C : Type) (Δ : Context)
  → ∀ {A B} (L : Γ ++ Δ , A ⊢ B)
  → rename (ext (weak Δ {C})) (subst (exts (extss Δ σ)) L)
    ≡ rename (weak (Δ , A)) (subst (extss (Δ , A) σ) L)
dsvh1a σ C Δ L =
  ≡begin
    rename (ext (weak Δ)) (subst (exts (extss Δ σ)) L)
  ≡⟨ cong (rename _) (cong-subst (exts-extss Δ σ) L) ⟩
    rename (ext (weak Δ)) (subst (extss (Δ , _) σ) L)
  ≡⟨ cong-rename (ext-weak Δ) (subst _ L) ⟩
    rename (weak (Δ , _)) (subst (extss (Δ , _) σ) L)
  ≡∎

dsvh1b : ∀ {Γ Γ′} (σ : ∀ {A} → Γ ∋ A → Γ′ ⊢ A) (C : Type) (Δ : Context)
  → ∀ {A B} (L : Γ ++ Δ , A ⊢ B)
  → subst (exts (extss Δ (exts σ {C}))) (rename (ext (weak Δ)) L)
    ≡ subst (extss (Δ , A) (exts σ)) (rename (weak (Δ , A)) L)
dsvh1b σ C Δ L =
  ≡begin
    subst (exts (extss Δ (exts σ))) (rename (ext (weak Δ)) L)
  ≡⟨ cong (subst _) (cong-rename (ext-weak Δ) L) ⟩
    subst (exts (extss Δ (exts σ))) (rename (weak (Δ , _)) L)
  ≡⟨ cong-subst (exts-extss Δ (exts σ)) (rename _ L) ⟩
    subst (extss (Δ , _) (exts σ)) (rename (weak (Δ , _)) L)
  ≡∎

dsvh2a : ∀ {Γ Γ′} (σ : ∀ {A} → Γ ∋ A → Γ′ ⊢ A) (D : Type) (Δ : Context)
  → ∀ {A B C} (L : Γ ++ Δ , A , B ⊢ C)
  → rename (ext (ext (weak Δ {D}))) (subst (exts (exts (extss Δ σ))) L)
    ≡ rename (weak (Δ , A , B)) (subst (extss (Δ , A , B) σ) L)
dsvh2a σ D Δ L =
  ≡begin
    rename (ext (ext (weak Δ))) (subst (exts (exts (extss Δ σ))) L)
  ≡⟨ cong (rename _) (cong-subst (cong-exts (exts-extss Δ σ)) L) ⟩
    rename (ext (ext (weak Δ))) (subst (exts (extss (Δ , _) σ)) L)
  ≡⟨ cong (rename _) (cong-subst (exts-extss (Δ , _) σ) L) ⟩
    rename (ext (ext (weak Δ))) (subst (extss (Δ , _ , _) σ) L)
  ≡⟨ cong-rename (cong-ext (ext-weak Δ)) _ ⟩
    rename (ext (weak (Δ , _))) (subst (extss (Δ , _ , _) σ) L)
  ≡⟨ cong-rename (ext-weak (Δ , _)) _ ⟩
    rename (weak (Δ , _ , _)) (subst (extss (Δ , _ , _) σ) L)
  ≡∎

dsvh2b : ∀ {Γ Γ′} (σ : ∀ {A} → Γ ∋ A → Γ′ ⊢ A) (D : Type) (Δ : Context)
  → ∀ {A B C} (L : Γ ++ Δ , A , B ⊢ C)
  → subst (exts (exts (extss Δ (exts σ {D})))) (rename (ext (ext (weak Δ))) L)
    ≡ subst (extss (Δ , A , B) (exts σ)) (rename (weak (Δ , A , B)) L)
dsvh2b σ D Δ L =
  ≡begin
    subst (exts (exts (extss Δ (exts σ)))) (rename (ext (ext (weak Δ))) L)
  ≡⟨ cong (subst _) (cong-rename (cong-ext (ext-weak Δ)) L) ⟩
    subst (exts (exts (extss Δ (exts σ)))) (rename (ext (weak (Δ , _))) L)
  ≡⟨ cong (subst _) (cong-rename (ext-weak (Δ , _)) L)⟩
    subst (exts (exts (extss Δ (exts σ)))) (rename (weak (Δ , _ , _)) L)
  ≡⟨ cong-subst (cong-exts (exts-extss Δ (exts σ))) (rename (weak (Δ , _ , _)) L) ⟩
    subst (exts (extss (Δ , _) (exts σ))) (rename (weak (Δ , _ , _)) L)
  ≡⟨ cong-subst (exts-extss (Δ , _) (exts σ)) (rename (weak (Δ , _ , _)) L) ⟩
    subst (extss (Δ , _ , _) (exts σ)) (rename (weak (Δ , _ , _)) L)
  ≡∎

dsvh : ∀ {Γ Γ′} (σ : ∀ {A} → Γ ∋ A → Γ′ ⊢ A) (B : Type)
  → ∀ (Δ : Context) {A} (L : Γ ++ Δ ⊢ A)
  → rename (weak Δ) (subst (extss Δ σ) L)
    ≡ subst (extss Δ (exts σ {B})) (rename (weak Δ) L)
dsvh σ B Δ (` x) = rename-weak-extss≡extss-exts-weak σ B Δ x
dsvh σ B Δ (ƛ_ L)
  rewrite dsvh1a σ B Δ L | dsvh σ B (Δ , _) L | dsvh1b σ B Δ L = refl
dsvh σ B Δ (M · N)
  rewrite dsvh σ B Δ M | dsvh σ B Δ N = refl
dsvh σ B Δ `zero = refl
dsvh σ B Δ (`suc L)
  rewrite dsvh σ B Δ L = refl
dsvh σ B Δ (case L M N)
  rewrite dsvh σ B Δ L | dsvh σ B Δ M
  | dsvh1a σ B Δ N | dsvh σ B (Δ , _) N | dsvh1b σ B Δ N
  = refl
dsvh σ B Δ (μ L)
  rewrite dsvh1a σ B Δ L | dsvh σ B (Δ , _) L | dsvh1b σ B Δ L = refl
dsvh σ B Δ (con x) = refl
dsvh σ B Δ (M `* N)
  rewrite dsvh σ B Δ M | dsvh σ B Δ N = refl
dsvh σ B Δ (`let M N)
  rewrite dsvh σ B Δ M | dsvh1a σ B Δ N | dsvh σ B (Δ , _) N | dsvh1b σ B Δ N = refl
dsvh σ B Δ `⟨ M , N ⟩
  rewrite dsvh σ B Δ M | dsvh σ B Δ N = refl
dsvh σ B Δ (`proj₁ L)
  rewrite dsvh σ B Δ L = refl
dsvh σ B Δ (`proj₂ L)
  rewrite dsvh σ B Δ L = refl
dsvh σ B Δ (case× M N)
  rewrite dsvh σ B Δ M | dsvh2a σ B Δ N | dsvh σ B (Δ , _ , _) N | dsvh2b σ B Δ N = refl
dsvh σ B Δ (`inj₁ L)
  rewrite dsvh σ B Δ L = refl
dsvh σ B Δ (`inj₂ L)
  rewrite dsvh σ B Δ L = refl
dsvh σ B Δ (case⊎ L M N)
  rewrite dsvh σ B Δ L
  | dsvh1a σ B Δ M | dsvh σ B (Δ , _) M | dsvh1b σ B Δ M
  | dsvh1a σ B Δ N | dsvh σ B (Δ , _) N | dsvh1b σ B Δ N
  = refl
dsvh σ B Δ `tt = refl
dsvh σ B Δ (case⊤ M N)
  rewrite dsvh σ B Δ M | dsvh σ B Δ N = refl
dsvh σ B Δ (case⊥ L)
  rewrite dsvh σ B Δ L = refl
dsvh σ B Δ `[] = refl
dsvh σ B Δ (M `∷ N)
  rewrite dsvh σ B Δ M | dsvh σ B Δ N = refl
dsvh σ B Δ (caseL L M N)
  rewrite dsvh σ B Δ L | dsvh σ B Δ M
  | dsvh2a σ B Δ N | dsvh σ B (Δ , _ , _) N | dsvh2b σ B Δ N
  = refl

dsv : ∀ {Γ A B C} (Δ : Context) (V : Γ ⊢ A) (W : Γ ⊢ B) (x : (Γ , A , B) ++ Δ ∋ C)
  → extss Δ (subst01 V W) x
    ≡ subst (extss Δ (substZero V)) (extss Δ (substZero (rename S_ W)) x)
dsv ∅ V W Z = sym (dsvZ ∅ V W)
dsv ∅ V W (S Z) = refl
dsv ∅ V W (S (S x)) = refl
dsv (Δ , D) V W Z = refl
dsv (Δ , D) V W (S x)
  rewrite dsv Δ V W x
  | dsvh (extss Δ (substZero V)) D ∅ (extss Δ (substZero (rename S_ W)) x)
  = cong-subst (exts-extss Δ (substZero V)) (rename S_ (extss Δ (substZero (rename S_ W)) x))

ds1a : ∀ {Γ A B C} (Δ : Context) {D}
  → ∀ (V : Γ ⊢ A) (W : Γ ⊢ B) (N : (Γ , A , B) ++ Δ , D ⊢ C)
  → subst (exts (extss Δ (subst01 V W))) N ≡ subst (extss (Δ , D) (subst01 V W)) N
ds1a Δ V W N = cong-subst (exts-extss Δ (subst01 V W)) N

ds1b : ∀ {Γ A B C} (Δ : Context) {D}
  → ∀ (V : Γ ⊢ A) (W : Γ ⊢ B) (N : (Γ , A , B) ++ Δ , D ⊢ C)
  → subst (exts (extss Δ (substZero V))) (subst (exts (extss Δ (substZero (rename S_ W)))) N)
    ≡ subst (extss (Δ , D) (substZero V)) (subst (extss (Δ , D) (substZero (rename S_ W))) N)
ds1b Δ {D} V W N =
  ≡begin
    subst (exts (extss Δ _)) (subst (exts (extss Δ _)) N)
      ≡⟨ cong (subst _) (cong-subst (exts-extss Δ _) N) ⟩
    subst (exts (extss Δ _)) (subst (extss (Δ , D) _) N)
      ≡⟨ cong-subst (exts-extss Δ _) (subst (extss (Δ , D) _) N) ⟩
    subst (extss (Δ , D) _) (subst (extss (Δ , D) _) N)
  ≡∎

ds2a : ∀ {Γ A B C} (Δ : Context) {D E}
  → ∀ (V : Γ ⊢ A) (W : Γ ⊢ B) (N : (Γ , A , B) ++ Δ , D , E ⊢ C)
  → subst (exts (exts (extss Δ (subst01 V W)))) N
    ≡ subst (extss (Δ , D , E) (subst01 V W)) N
ds2a Δ {D} {E} V W N = cong-subst (λ x →
    ≡begin
      exts (exts (extss Δ _)) x
    ≡⟨ cong-exts (exts-extss Δ _) x ⟩
      exts (extss (Δ , D) _) x
    ≡⟨ exts-extss (Δ , D) _ x ⟩
      extss (Δ , D , E) _ x
    ≡∎
  ) N

ds2b : ∀ {Γ A B C} (Δ : Context) {D E}
  → ∀ (V : Γ ⊢ A) (W : Γ ⊢ B) (N : (Γ , A , B) ++ Δ , D , E ⊢ C)
  → subst (exts (exts (extss Δ (substZero V))))
      (subst (exts (exts (extss Δ (substZero (rename S_ W))))) N)
    ≡ subst (extss (Δ , D , E) (substZero V))
      (subst (extss (Δ , D , E) (substZero (rename S_ W))) N)
ds2b Δ {D} {E} V W N =
  ≡begin
    subst (exts (exts (extss Δ _))) (subst (exts (exts (extss Δ _))) N)
  ≡⟨ cong (subst _) (cong-subst (cong-exts (exts-extss Δ _)) N) ⟩
    subst (exts (exts (extss Δ _))) (subst (exts (extss (Δ , D) _)) N)
  ≡⟨ cong (subst _) (cong-subst (exts-extss (Δ , D) _) N) ⟩
    subst (exts (exts (extss Δ _))) (subst (extss (Δ , D , E) _) N)
  ≡⟨ cong-subst (cong-exts (exts-extss Δ _)) (subst (extss (Δ , D , E) _) N) ⟩
    subst (exts (extss (Δ , D) _)) (subst (extss (Δ , D , E) _) N)
  ≡⟨ cong-subst (exts-extss (Δ , D) _) (subst (extss (Δ , D , E) _) N) ⟩
    subst (extss (Δ , D , E) _) (subst (extss (Δ , D , E) _) N)
  ≡∎

ds : ∀ {Γ A B C} (Δ : Context) (V : Γ ⊢ A) (W : Γ ⊢ B) (N : (Γ , A , B) ++ Δ ⊢ C)
  → subst (extss Δ (subst01 V W)) N
    ≡ subst (extss Δ (substZero V)) (subst (extss Δ (substZero (rename S_ W))) N)
ds Δ V W (` x) = dsv Δ V W x
ds Δ V W (ƛ N)
  rewrite ds1a Δ V W N | ds (Δ , _) V W N | ds1b Δ V W N = refl
ds Δ V W (M · N)
  rewrite ds Δ V W M | ds Δ V W N = refl
ds Δ V W `zero = refl
ds Δ V W (`suc N)
  rewrite ds Δ V W N = refl
ds Δ V W (case L M N)
  rewrite ds Δ V W L | ds Δ V W M | ds1a Δ V W N | ds (Δ , _) V W N | ds1b Δ V W N = refl
ds Δ V W (μ N)
  rewrite ds1a Δ V W N | ds (Δ , _) V W N | ds1b Δ V W N = refl
ds Δ V W (con x) = refl
ds Δ V W (M `* N)
  rewrite ds Δ V W M | ds Δ V W N = refl
ds Δ V W (`let M N)
  rewrite ds Δ V W M | ds1a Δ V W N | ds (Δ , _) V W N | ds1b Δ V W N = refl
ds Δ V W `⟨ M , N ⟩
  rewrite ds Δ V W M | ds Δ V W N = refl
ds Δ V W (`proj₁ N)
  rewrite ds Δ V W N = refl
ds Δ V W (`proj₂ N)
  rewrite ds Δ V W N = refl
ds Δ V W (case× M N)
  rewrite ds Δ V W M | ds2a Δ V W N | ds (Δ , _ , _) V W N | ds2b Δ V W N = refl
ds Δ V W (`inj₁ N)
  rewrite ds Δ V W N = refl
ds Δ V W (`inj₂ N)
  rewrite ds Δ V W N = refl
ds Δ V W (case⊎ L M N)
  rewrite ds Δ V W L
  | ds1a Δ V W M | ds (Δ , _) V W M | ds1b Δ V W M
  | ds1a Δ V W N | ds (Δ , _) V W N | ds1b Δ V W N
  = refl
ds Δ V W `tt = refl
ds Δ V W (case⊤ M N)
  rewrite ds Δ V W M | ds Δ V W N = refl
ds Δ V W (case⊥ N)
  rewrite ds Δ V W N = refl
ds Δ V W `[] = refl
ds Δ V W (M `∷ N)
  rewrite ds Δ V W M | ds Δ V W N = refl
ds Δ V W (caseL L M N)
  rewrite ds Δ V W L | ds Δ V W M | ds2a Δ V W N | ds (Δ , _ , _) V W N | ds2b Δ V W N = refl

double-subst {Γ} {A} {B} {C} {V} {W} {N} =
  ≡begin
    N [ V ][ W ]
  ≡⟨ helper ⟩
    subst (subst01 V W) N
  ≡⟨ ds ∅ V W N ⟩
    subst (substZero V) (subst (substZero (rename S_ W)) N)
  ≡⟨⟩
    (N [ rename S_ W ]) [ V ]
  ≡∎
  where
  helper : N [ V ][ W ] ≡ subst (subst01 V W) N
  helper = cong-subst (λ{ Z → refl ; (S Z) → refl ; (S (S x)) → refl }) N
```

## Test examples

We repeat the [test examples](/DeBruijn/#examples) from Chapter [DeBruijn](/DeBruijn/),
in order to make sure we have not broken anything in the process of extending our base calculus.
```agda
two : ∀ {Γ} → Γ ⊢ `ℕ
two = `suc `suc `zero

plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
plus = μ ƛ ƛ (case (# 1) (# 0) (`suc (# 3 · # 0 · # 1)))

2+2 : ∀ {Γ} → Γ ⊢ `ℕ
2+2 = plus · two · two

Ch : Type → Type
Ch A  =  (A ⇒ A) ⇒ A ⇒ A

twoᶜ : ∀ {Γ A} → Γ ⊢ Ch A
twoᶜ = ƛ ƛ (# 1 · (# 1 · # 0))

plusᶜ : ∀ {Γ A} → Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A
plusᶜ = ƛ ƛ ƛ ƛ (# 3 · # 1 · (# 2 · # 1 · # 0))

sucᶜ : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ
sucᶜ = ƛ `suc (# 0)

2+2ᶜ : ∀ {Γ} → Γ ⊢ `ℕ
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
```

## Unicode

This chapter uses the following unicode:

    σ  U+03C3  GREEK SMALL LETTER SIGMA (\Gs or \sigma)
    †  U+2020  DAGGER (\dag)
    ‡  U+2021  DOUBLE DAGGER (\ddag)
