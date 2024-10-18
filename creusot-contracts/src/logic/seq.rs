use crate::{
    invariant::*,
    logic::{ops::IndexLogic, Mapping},
    *,
};

#[trusted]
#[cfg_attr(creusot, creusot::builtins = "seq.Seq.seq")]
pub struct Seq<T: ?Sized>(std::marker::PhantomData<T>);

impl<T: ?Sized> Seq<T> {
    #[cfg(creusot)]
    #[trusted]
    #[creusot::builtins = "seq.Seq.empty"]
    pub const EMPTY: Self = { Seq(std::marker::PhantomData) };

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "seq.Seq.create"]
    pub fn new(_: Int, _: Mapping<Int, T>) -> Self {
        absurd
    }

    #[logic]
    #[open]
    pub fn get(self, ix: Int) -> Option<T>
    where
        T: Sized, // TODO : don't require this (problem: return type needs to be sized)
    {
        if 0 <= ix && ix < self.len() {
            Some(self.index_logic(ix))
        } else {
            None
        }
    }

    #[trusted]
    #[logic]
    #[open]
    #[creusot::builtins = "seq.Seq.get"]
    pub fn index_logic_unsized(self, _: Int) -> Box<T> {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "seq.Seq.([..])"]
    pub fn subsequence(self, _: Int, _: Int) -> Self {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "seq.Seq.singleton"]
    pub fn singleton(_: T) -> Self {
        absurd
    }

    #[logic]
    #[open]
    pub fn tail(self) -> Self {
        self.subsequence(1, self.len())
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[rustc_diagnostic_item = "seq_len"]
    #[creusot::builtins = "seq.Seq.length"]
    pub fn len(self) -> Int {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "seq.Seq.set"]
    pub fn set(self, _: Int, _: T) -> Self {
        absurd
    }

    #[trusted]
    #[predicate]
    #[open(self)]
    #[creusot::builtins = "seq.Seq.(==)"]
    pub fn ext_eq(self, _: Self) -> bool {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "seq.Seq.snoc"]
    pub fn push(self, _: T) -> Self {
        absurd
    }

    // FIXME: order of arguments
    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "seq.Seq.cons"]
    pub fn push_front(_: T, _: Self) -> Self {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "seq.Seq.(++)"]
    pub fn concat(self, _: Self) -> Self {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "seq.Reverse.reverse"]
    pub fn reverse(self) -> Self {
        absurd
    }

    #[predicate]
    #[open]
    pub fn permutation_of(self, o: Self) -> bool {
        self.permut(o, 0, self.len())
    }

    #[trusted]
    #[predicate]
    #[open(self)]
    #[creusot::builtins = "seq.Permut.permut"]
    pub fn permut(self, _: Self, _: Int, _: Int) -> bool {
        absurd
    }

    #[trusted]
    #[predicate]
    #[open(self)]
    #[creusot::builtins = "seq.Permut.exchange"]
    pub fn exchange(self, _: Self, _: Int, _: Int) -> bool {
        absurd
    }

    #[open]
    #[predicate]
    pub fn contains(self, e: T) -> bool
    where
        T: Sized, // TODO : don't require this (problem: uses index)
    {
        pearlite! { exists<i : Int> 0 <= i &&  i < self.len() && self[i] == e }
    }

    #[open]
    #[predicate]
    pub fn sorted_range(self, l: Int, u: Int) -> bool
    where
        T: OrdLogic + Sized, // TODO : don't require this (problem: uses index)
    {
        pearlite! {
            forall<i : Int, j : Int> l <= i && i <= j && j < u ==> self[i] <= self[j]
        }
    }

    #[open]
    #[predicate]
    pub fn sorted(self) -> bool
    where
        T: OrdLogic + Sized, // TODO : don't require this (problem: uses index)
    {
        self.sorted_range(0, self.len())
    }
}

/// Ghost definitions
impl<T> Seq<T> {
    /// Constructs a new, empty `Seq<T>`.
    ///
    /// This is allocated on the ghost heap, and as such is wrapped in [`GhostBox`].
    ///
    /// # Example
    ///
    /// ```rust,creusot
    /// use creusot_contracts::{proof_assert, Seq};
    /// let ghost_seq = Seq::<i32>::new_ghost();
    /// proof_assert!(seq == Seq::new());
    /// ```
    #[trusted]
    #[pure]
    #[ensures(*result == Self::EMPTY)]
    pub fn new_ghost() -> GhostBox<Self> {
        #[cfg(creusot)]
        {
            loop {}
        }
        #[cfg(not(creusot))]
        {
            GhostBox(::std::marker::PhantomData)
        }
    }

    /// Returns the number of elements in the vector, also referred to as its 'length'.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost, proof_assert, Seq};
    ///
    /// let mut vec = Seq::new_ghost();
    /// let length = ghost! {
    ///     vec.push(1);
    ///     vec.push(2);
    ///     vec.push(3);
    ///     vec.len()
    /// };
    /// proof_assert!(length.inner() == 3);
    /// ```
    #[trusted]
    #[pure]
    #[ensures(result == self.len())]
    pub fn len_ghost(&self) -> Int {
        loop {}
    }

    /// Appends an element to the back of a collection.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost, proof_assert, Seq};
    ///
    /// let mut s = Seq::new_ghost();
    /// ghost! {
    ///     s.push(1);
    ///     s.push(2);
    ///     s.push(3);
    /// };
    /// proof_assert!(s[0] == 1i32 && s[1] == 2i32 && s[2] == 3i32);
    /// ```
    #[trusted]
    #[pure]
    #[ensures(^self == self.push(x))]
    pub fn push_ghost(&mut self, x: T) {
        let _ = x;
        loop {}
    }

    #[trusted]
    #[pure]
    #[ensures(^self == Seq::push_front(x, *self))]
    pub fn push_front_ghost(&mut self, x: T) {
        let _ = x;
        loop {}
    }

    /// Returns a reference to an element at `index` or `None` if `index` is out of bounds.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost, Int, proof_assert, Seq};
    ///
    /// let mut s = Seq::new_ghost();
    /// let gets = ghost! {
    ///     s.push(10);
    ///     s.push(40);
    ///     s.push(30);
    ///     let get1 = s.get(*Int::new(1));
    ///     let get2 = s.get(*Int::new(3));
    ///     (get1, get2)
    /// };
    /// proof_assert!(gets.inner().0 == Some(&40i32));
    /// proof_assert!(gets.inner().1 == None);
    /// ```
    #[trusted]
    #[pure]
    #[ensures(match self.get(index) {
        None => result == None,
        Some(v) => result == Some(&v),
    })]
    pub fn get_ghost(&self, index: Int) -> Option<&T> {
        let _ = index;
        loop {}
    }

    /// Returns a mutable reference to an element at `index` or `None` if `index` is out of bounds.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost, Int, proof_assert, Seq};
    ///
    /// let mut s = Seq::new_ghost();
    ///
    /// ghost! {
    ///     s.push(0);
    ///     s.push(1);
    ///     s.push(2);
    ///     if let Some(elem) = s.get_mut(*Int::new(1)) {
    ///         *elem = 42;
    ///     }
    /// };
    /// proof_assert!(s[0] == 0i32 && s[1] == 42i32 && s[2] == 2i32);
    /// ```
    #[trusted]
    #[pure]
    #[ensures(if self.get(index) == None {
        result == None && *self == ^self
    } else {
        match result {
            None => false,
            Some(r) => *r == (*self)[index] && ^r == (^self)[index]
        }
    })]
    #[ensures(forall<i: Int> i != index ==> (*self).get(index) == (^self).get(index))]
    #[ensures((*self).len() == (^self).len())]
    pub fn get_mut_ghost(&mut self, index: Int) -> Option<&mut T> {
        let _ = index;
        loop {}
    }

    /// Removes the last element from a vector and returns it, or `None` if it is empty.
    ///
    /// # Example
    /// ```rust,creusot
    /// use creusot_contracts::{ghost, proof_assert, Seq};
    ///
    /// let mut s = Seq::new_ghost();
    /// let popped = ghost! {
    ///     s.push(1);
    ///     s.push(2);
    ///     s.push(3);
    ///     s.pop()
    /// };
    /// proof_assert!(popped == Some(3i32));
    /// proof_assert!(s[0] == 1i32 && s[1] == 2i32);
    /// ```
    #[trusted]
    #[pure]
    #[ensures(if self.len() == 0 {
        *self == ^self && result == None
    } else {
        match result {
            None => false,
            Some(r) => *self == (^self).push(r)
        }
    })]
    pub fn pop_ghost(&mut self) -> Option<T> {
        loop {}
    }

    #[trusted]
    #[pure]
    #[ensures(if self.len() == 0 {
        *self == ^self && result == None
    } else {
        match result {
            None => false,
            Some(r) => *self == Seq::singleton(r).concat(^self)
        }
    })]
    pub fn pop_front_ghost(&mut self) -> Option<T> {
        loop {}
    }
}

impl<T: ?Sized> Seq<&T> {
    #[logic]
    #[open]
    #[trusted]
    #[creusot::builtins = "identity"]
    pub fn to_owned_seq(self) -> Seq<T> {
        pearlite! {absurd}
    }
}

impl<T> IndexLogic<Int> for Seq<T> {
    type Item = T;

    #[logic]
    #[trusted]
    #[open(self)]
    #[rustc_diagnostic_item = "seq_index"]
    #[creusot::builtins = "seq.Seq.get"]
    fn index_logic(self, _: Int) -> Self::Item {
        absurd
    }
}

impl<T: ?Sized> Invariant for Seq<T> {
    #[predicate(prophetic)]
    #[open]
    #[creusot::trusted_ignore_structural_inv]
    #[creusot::trusted_is_tyinv_trivial_if_param_trivial]
    fn invariant(self) -> bool {
        pearlite! { forall<i:Int> 0 <= i && i < self.len() ==> inv(self.index_logic_unsized(i)) }
    }
}
