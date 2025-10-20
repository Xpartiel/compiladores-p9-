package com.compiler.parser.lr;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import com.compiler.parser.grammar.Grammar;
import com.compiler.parser.grammar.Symbol;

/**
 * Builds the canonical collection of LR(1) items (the DFA automaton).
 * Items contain a lookahead symbol.
 */
public class LR1Automaton {
    private final Grammar grammar;
    private final List<Set<LR1Item>> states = new ArrayList<>();
    private final Map<Integer, Map<Symbol, Integer>> transitions = new HashMap<>();
    private String augmentedLeftName = null;

    public LR1Automaton(Grammar grammar) {
        this.grammar = Objects.requireNonNull(grammar);
    }

    public List<Set<LR1Item>> getStates() { return states; }
    public Map<Integer, Map<Symbol, Integer>> getTransitions() { return transitions; }

    /**
     * CLOSURE for LR(1): standard algorithm using FIRST sets to compute lookaheads for new items.
     */
    private Set<LR1Item> closure(Set<LR1Item> items) {
        // TODO: Implement the CLOSURE algorithm for a set of LR(1) items.
        // 1. Initialize a new set `closure` with the given `items`.
        // 2. Create a worklist (like a Queue or List) and add all items from `items` to it.
        // 3. Pre-calculate the FIRST sets for all symbols in the grammar.
        // 4. While the worklist is not empty:
        //    a. Dequeue an item `[A -> α • B β, a]`.
        //    b. If `B` is a non-terminal:
        //       i. For each production of `B` (e.g., `B -> γ`):
        //          - Calculate the FIRST set of the sequence `βa`. This will be the lookahead for the new item.
        //          - For each terminal `b` in FIRST(βa):
        //             - Create a new item `[B -> • γ, b]`.
        //             - If this new item is not already in the `closure` set:
        //               - Add it to `closure`.
        //               - Enqueue it to the worklist.
        // 5. Return the `closure` set.
        return new HashSet<>(); // Placeholder
    }

    /**
     * Compute FIRST of a sequence of symbols.
     */
    private Set<Symbol> computeFirstOfSequence(List<Symbol> seq, Map<Symbol, Set<Symbol>> firstSets, Symbol epsilon) {
        // TODO: Implement the logic to compute the FIRST set for a sequence of symbols.
        // 1. Initialize an empty result set.
        // 2. If the sequence is empty, add epsilon to the result and return.
        // 3. Iterate through the symbols `X` in the sequence:
        //    a. Get `FIRST(X)` from the pre-calculated `firstSets`.
        //    b. Add all symbols from `FIRST(X)` to the result, except for epsilon.
        //    c. If `FIRST(X)` does not contain epsilon, stop and break the loop.
        //    d. If it does contain epsilon and this is the last symbol in the sequence, add epsilon to the result set.
        // 4. Return the result set.
        return new HashSet<>(); // Placeholder
    }

    /**
     * GOTO for LR(1): moves dot over symbol and takes closure.
     */
    private Set<LR1Item> goTo(Set<LR1Item> state, Symbol symbol) {
        // TODO: Implement the GOTO function.
        // 1. Initialize an empty set `movedItems`.
        // 2. For each item `[A -> α • X β, a]` in the input `state`:
        //    a. If `X` is equal to the input `symbol`:
        //       - Add the new item `[A -> α X • β, a]` to `movedItems`.
        // 3. Return the `closure` of `movedItems`.
        return new HashSet<>(); // Placeholder
    }

    /**
     * Build the LR(1) canonical collection: states and transitions.
     */
    public void build() {
        // TODO: Implement the construction of the canonical collection of LR(1) item sets (the DFA).
        // 1. Clear any existing states and transitions.
        // 2. Create the augmented grammar: Add a new start symbol S' and production S' -> S.
        // 3. Create the initial item: `[S' -> • S, $]`.
        // 4. The first state, `I0`, is the `closure` of this initial item set. Add `I0` to the list of states.
        // 5. Create a worklist (queue) and add `I0` to it.
        // 6. While the worklist is not empty:
        //    a. Dequeue a state `I`.
        //    b. For each grammar symbol `X`:
        //       i. Calculate `J = goTo(I, X)`.
        //       ii. If `J` is not empty and not already in the list of states:
        //          - Add `J` to the list of states.
        //          - Enqueue `J` to the worklist.
        //       iii. Create a transition from the index of state `I` to the index of state `J` on symbol `X`.
    }

    public String getAugmentedLeftName() { return augmentedLeftName; }
}
