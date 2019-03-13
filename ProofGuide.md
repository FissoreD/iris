# Iris Proof Guide

This work-in-progress document serves to explain how Iris proofs are typically
carried out in Coq: what are the common patterns, what are the common pitfalls.
This complements the tactic documentation for the [proof mode](ProofMode.md) and
[HeapLang](HeapLang.md) as well as the documentation of syntactic conventions in
the [style guide](StyleGuide.md).

## Resource algebra management

When using ghost state in Iris, you have to make sure that the resource algebras
you need are actually available.  Every Iris proof is carried out using a
universally quantified list `Σ: gFunctors` defining which resource algebras are
available.  You can think of this as a list of resource algebras, though in
reality it is a list of functors from OFEs to Cameras (where Cameras are a
step-indexed generalization of resource algebras).  This is the *global* list of
resources that the entire proof can use.  We keep it universally quantified to
enable composition of proofs.  The formal side of this is described in §7.4 of
[The Iris Documentation](http://plv.mpi-sws.org/iris/appendix-3.1.pdf); here we
describe the Coq aspects of this approach.

The assumptions that an Iris proof makes are collected in a type class called
`somethingG`.  The most common kind of assumptions is `inG`, which says that a
particular resource algebra is available for ghost state.  For example, in the
[one-shot example](tests/one_shot.v):
```
Class one_shotG Σ := { one_shot_inG :> inG Σ one_shotR }.
```
The `:>` means that the projection `one_shot_inG` is automatically registered as
an instance for type-class resolution.  If you need several resource algebras,
just add more `inG` fields.  If you are using another module as part of yours,
add a field like `one_shot_other :> otherG Σ`.

Having defined the type class, we need to provide a way to instantiate it.  This
is an important step, as not every resource algebra can actually be used: if
your resource algebra refers to `Σ`, the definition becomes recursive.  That is
actually legal under some conditions (which is why the global list `Σ` contains
functors and not just resource algebras), but for the purpose of this guide we
will ignore that case.  We have to define a list that contains all the resource
algebras we need:
```
Definition one_shotΣ : gFunctors := #[GFunctor one_shotR].
```
This time, there is no `Σ` in the context, so we cannot accidentally introduce a
bad dependency.  If you are using another module as part of yours, add their
`somethingΣ` to yours, as in `#[GFunctor one_shotR; somethingΣ]`.  (The
`#[F1; F2; ...]` syntax *appends* the functor lists `F1`, `F2`, ... to each
other; together with a coercion from a single functor to a singleton list, this
means lists can be nested arbitrarily.)

Now we can define the one and only instance that our type class will ever need:
```
Instance subG_one_shotΣ {Σ} : subG one_shotΣ Σ → one_shotG Σ.
Proof. solve_inG. Qed.
```
The `subG` assumption here says that the list `one_shotΣ` is a sublist of the
global list `Σ`.  Typically, this should be the only assumption your instance
needs, showing that the assumptions of the module (and all the modules it
uses internally) can trivially be satisfied by picking the right `Σ`.

Now you can add `one_shotG` as an assumption to all your module definitions and
proofs.  We typically use a section for this:
```
Section proof.
Context `{!heapG Σ, !one_shotG Σ}.
```
Notice that besides our own assumptions `one_shotG`, we also assume `heapG`,
which are assumptions that every HeapLang proof makes (they are related to
defining the `↦` connective as well as the basic Iris infrastructure for
invariants and WP).  For this purpose, `heapG` contains not only assumptions
about `Σ`, it also contains some ghost names to refer to particular ghost state
(see "global ghost state instances" below).

The backtic (`` ` ``) is used to make anonymous assumptions and to automatically
generalize the `Σ`.  When adding assumptions with backtic, you should most of
the time also add a `!` in front of every assumption.  If you do not then Coq
will also automatically generalize all indices of type-classes that you are
assuming.  This can easily lead to making more assumptions than you are aware
of, and often it leads to duplicate assumptions which breaks type class
resolutions.

### Obtaining a closed proof

To obtain a closed Iris proof, i.e., a proof that does not make assumptions like
`inG`, you have to assemble a list of functors of all the involved modules,
and if your proof relies on some singleton (most do, at least indirectly; also
see the next section), you have to call the respective initialization or
adequacy lemma.  [For example](tests/one_shot.v):
```
Section client.
  Context `{!heapG Σ, !one_shotG Σ, !spawnG Σ}.

  Lemma client_safe : WP client {{ _, True }}%I.
  (* ... *)
End client.

(** Assemble all functors needed by the [client_safe] proof. *)
Definition clientΣ : gFunctors := #[ heapΣ; one_shotΣ; spawnΣ ].

(** Apply [heap_adequacy] with this list of all functors. *)
Lemma client_adequate σ : adequate NotStuck client σ (λ _ _, True).
Proof. apply (heap_adequacy clientΣ)=> ?. apply client_safe. Qed.
```

### Advanced topic: Ghost state singletons

Some Iris modules involve a form of "global state".  For example, defining the
`↦` for HeapLang involves a piece of ghost state that matches the current
physical heap.  The `gname` of that ghost state must be picked once when the
proof starts, and then globally known everywhere.  Hence it is added to
`gen_heapG`, the type class for the generalized heap module:
```
Class gen_heapG (L V : Type) (Σ : gFunctors) `{Countable L} := {
  gen_heap_inG :> inG Σ (authR (gen_heapUR L V));
  gen_heap_name : gname
}.
```

Such modules always need some kind of "initialization" to create an instance
of their type class.  For example, the initialization for `heapG` is happening
as part of [`heap_adequacy`](theories/heap_lang/adequacy.v); this in turn uses
the initialization lemma for `gen_heapG` from
[`gen_heap_init`](theories/base_logic/lib/gen_heap.v):
```
Lemma gen_heap_init `{gen_heapPreG L V Σ} σ :
  (|==> ∃ _ : gen_heapG L V Σ, gen_heap_ctx σ)%I.
```
These lemmas themselves only make assumptions the way normal modules (those
without global state) do, which are typically collected in a `somethingPreG`
type class (such as `gen_heapPreG`):
```
Class gen_heapPreG (L V : Type) (Σ : gFunctors) `{Countable L} := {
  gen_heap_preG_inG :> inG Σ (authR (gen_heapUR L V))
}.
```
Just like in the normal case, `somethingPreG` type classes have an `Instance`
showing that a `subG` is enough to instantiate them:
```
Instance subG_gen_heapPreG {Σ L V} `{Countable L} :
  subG (gen_heapΣ L V) Σ → gen_heapPreG L V Σ.
Proof. solve_inG. Qed.
```
The initialization lemma then shows that the `somethingPreG` type class is
enough to create an instance of the main `somethingG` class *below a view
shift*.  This is written with an existential quantifier in the lemma because the
statement after the view shift (`gen_heap_ctx σ` in this case) depends on having
an instance of `gen_heapG` in the context.

Given that these global ghost state instances are singletons, they must be
assumed explicitly everywhere.  Bundling `heapG` in a module type class like
`one_shotG` would lose track of the fact that there exists just one `heapG`
instance that is shared by everyone.

### Advanced topic: Additional module assumptions

Some modules need additional assumptions.  For example, the STS module is
parameterized by an STS and assumes that the STS state space is inhabited:
```
Class stsG Σ (sts : stsT) := {
  sts_inG :> inG Σ (stsR sts);
  sts_inhabited :> Inhabited (sts.state sts);
}.
```
In this rather exceptional case, the `Instance` for this class has more than
just a `subG` assumption:
```
Instance subG_stsΣ Σ sts :
  subG (stsΣ sts) Σ → Inhabited (sts.state sts) → stsG Σ sts.
```
If users of this module follow the pattern described above, their own type class
instance will check these additional assumption.  But this is one more reason
why it is important for every module to have an instance for its `somethingG`:
to make sure that it does not accidentally make more assumptions than it intends
to.

Another subtle detail here is that the `subG` assumption comes first in
`subG_stsΣ`, i.e., it appears before the `Inhabited`.  This is important because
otherwise, `sts_inhabited` and `subG_stsΣ` form an instance cycle that makes
type class search diverge.

## Canonical structures and type classes

In Iris, we use both canonical structures and type classes, and some careful
tweaking is necessary to make the two work together properly.  The details of
this still need to be written up properly, but here is some background material:

* [Type Classes for Mathematics in Type Theory](http://www.eelis.net/research/math-classes/mscs.pdf)
* [Canonical Structures for the working Coq user](https://hal.inria.fr/hal-00816703v1/document)
