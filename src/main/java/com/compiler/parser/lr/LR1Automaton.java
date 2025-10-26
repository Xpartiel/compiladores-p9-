package com.compiler.parser.lr;

import java.nio.file.ProviderNotFoundException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Queue;
import java.util.Set;

import com.compiler.parser.grammar.Grammar;
import com.compiler.parser.grammar.Production;
import com.compiler.parser.grammar.Symbol;
import com.compiler.parser.grammar.SymbolType;
import com.compiler.parser.syntax.StaticAnalyzer;

/**
 * Builds the canonical collection of LR(1) items (the DFA automaton).
 * Items contain a lookahead symbol.
 */
public class LR1Automaton {
    private final Grammar grammar;
    private final List<Set<LR1Item>> states = new ArrayList<>();
    private final Map<Integer, Map<Symbol, Integer>> transitions = new HashMap<>();
    private String augmentedLeftName = null;

    //simbolo auxiliar epsilon.
    Symbol epsilon =  new Symbol("epsilon", SymbolType.TERMINAL);

    public LR1Automaton(Grammar grammar) {
        this.grammar = Objects.requireNonNull(grammar);
    }

    public List<Set<LR1Item>> getStates() { return states; }
    public Map<Integer, Map<Symbol, Integer>> getTransitions() { return transitions; }

    /**
     * CLOSURE for LR(1): standard algorithm using FIRST sets to compute lookaheads for new items.
     */
    private Set<LR1Item> closure(Set<LR1Item> items) {
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


        //Paso 1:
        HashSet<LR1Item> closure = new HashSet<>(items);
        
        //Paso 2:
        Queue<LR1Item> worklist = new LinkedList<>(items);

        //Paso3: 
        //para calcular el first
        StaticAnalyzer calc = new StaticAnalyzer(grammar);
        //calculamos el first de toda la gramatica.
        Map<Symbol, Set<Symbol>> first = calc.getFirstSets();

        // 4. While the worklist is not empty:
        // Paso 4:
        while (!worklist.isEmpty()){

            // a. Dequeue an item `[A -> α • B β, a]`.
            LR1Item item = worklist.poll();

            // b. If `B` is a non-terminal:
            Symbol characterB= item.getSymbolAfterDot();
            if( (characterB != null) && (characterB.type == SymbolType.NON_TERMINAL) ){ //puede ser que sea necesario verificar que no sea null

                //Primero obtenemos todas las producciones de B
                LinkedList<Production> productionsB = new LinkedList<>();
                for (Production prod : this.grammar.getProductions()){
                    if (prod.left.equals(characterB)){
                        productionsB.add(prod);
                    }
                }
                // i. For each production of `B` (e.g., `B -> γ`):
                for (Production production : productionsB){
                    //necesitamos un metodo auxilar que devuelva una secuencia (Lista de simbolos) a
                    //partir de la posicion del punto (aunque luego eliminaremos el final o el primero
                    //segun donde este el simbolo B).

                    //obtenemos la secuencia despues del punto.
                    LinkedList<Symbol>seq=this.productionPostDot(item);
                    //Eliminamos B para obtener la secuencia a partir de Beta
                    seq.remove(0);
                    //Añadimos el lookahead a la secuencia despues de beta.
                    seq.add(item.lookahead);
                    
                    //- Calculate the FIRST set of the sequence `βa`. This will be the lookahead for the new item.
                    Set<Symbol> newLookAhead = this.computeFirstOfSequence(seq, first,epsilon);
                    //- For each terminal `b` in FIRST(βa):
                    for (Symbol symbol : newLookAhead){
                        if(symbol.type==SymbolType.TERMINAL){
                            //             - Create a new item `[B -> • γ, b]`.
                            LR1Item newItem = new LR1Item(production, 0, symbol);

                            //             - If this new item is not already in the `closure` set:
                            //               - Add it to `closure`.
                            //               - Enqueue it to the worklist.
                            if (closure.add(item)){
                                worklist.add(item);
                            }

                        }
                        
                    }



                }   
            }            
        }
        
        // 5. Return the `closure` set.
        return closure;
    }

    /**
     * Compute FIRST of a sequence of symbols.
     * 
     * 1. Initialize an empty result set.
     * 2. If the sequence is empty, add epsilon to the result and return.
     * 3. Iterate through the symbols `X` in the sequence:
     *     a. Get `FIRST(X)` from the pre-calculated `firstSets`.
     *     b. Add all symbols from `FIRST(X)` to the result, except for epsilon.
     *     c. If `FIRST(X)` does not contain epsilon, stop and break the loop.
     *     d. If it does contain epsilon and this is the last symbol in the sequence, add epsilon to the result set.
     *  4. Return the result set.
     */
    private Set<Symbol> computeFirstOfSequence(List<Symbol> seq, Map<Symbol, Set<Symbol>> firstSets, Symbol epsilon) {
        
        // 1. Initialize an empty result set.
        HashSet<Symbol> res = new HashSet<>();
        
        // 2. If the sequence is empty, add epsilon to the result and return.
        if( seq.isEmpty() ){
            res.add(epsilon);
            return res;
        }

        boolean hasEpsilon;
        int reachedSymbols = 0;
        Set<Symbol> first;

        // 3. Iterate through the symbols `X` in the sequence:
        for( Symbol symbol : seq ){
            ++reachedSymbols;

            // a. Get `FIRST(X)` from the pre-calculated `firstSets`.
            first = firstSets.get( symbol );

            // b. Add all symbols from `FIRST(X)` to the result, except for epsilon.
            hasEpsilon = first.remove(epsilon);
            res.addAll(first);

            // c. If `FIRST(X)` does not contain epsilon, stop and break the loop.
            if( !hasEpsilon ){
                break;
            }

            // d. If it does contain epsilon and this is the last symbol in the sequence, add epsilon to the result set.
            if( reachedSymbols == seq.size() ){
                res.add(epsilon);
            }
        }
        // 4. Return the result set.
        return res;
    }

    /**
     * Auxiliar method that helps us find the symbol sequence after the
     * {@code dotPosition} from an {@link LR1Item}
     * @param item
     * @return
     */
    private LinkedList<Symbol> productionPostDot( LR1Item item ){
        // Initialize empty listing
        LinkedList<Symbol> res = new LinkedList<>();

        List<Symbol> productions = item.production.getRight();
        for (int i = item.dotPosition; i < productions.size(); i++){
            res.add( productions.get(i) );
        }
        return res;
    }

    /**
     * GOTO for LR(1): moves dot over symbol and takes closure.
     * 
     * 1. Initialize an empty set `movedItems`.
     * 2. For each item `[A -> α • X β, a]` in the input `state`:
     *    a. If `X` is equal to the input `symbol`:
     *       - Add the new item `[A -> α X • β, a]` to `movedItems`.
     * 3. Return the `closure` of `movedItems`.
     */
    private Set<LR1Item> goTo(Set<LR1Item> state, Symbol symbol) {

        // 1. Initialize an empty set `movedItems`.
        HashSet<LR1Item> movedItems = new HashSet<>();
        List<Symbol> postDot;
        Symbol X;

        // 2. For each item `[A -> α • X β, a]` in the input `state`:
        for ( LR1Item item : state ) {

            postDot = this.productionPostDot(item);
            // a. If `X` is equal to the input `symbol`:
            X = postDot.remove(0);
            if( X.equals(symbol) ){
                // - Add the new item `[A -> α X • β, a]` to `movedItems`.
                movedItems.add( new LR1Item(
                    item.production,
                    item.dotPosition+1,
                    item.lookahead));
            }
        }

        // 3. Return the `closure` of `movedItems`.
        return closure(movedItems);
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
