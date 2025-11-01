package com.compiler.parser.lr;

import com.compiler.parser.grammar.Symbol;
import com.compiler.parser.grammar.Production;
import com.compiler.parser.grammar.SymbolType;
import java.util.Set;
import java.util.Map;
import java.util.List;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.ArrayList;

/**
 * Builds the LALR(1) parsing table (ACTION/GOTO).
 * Main task for Practice 9.
 */
public class LALR1Table {
    private final LR1Automaton automaton;

    // merged LALR states and transitions
    private List<Set<LR1Item>> lalrStates = new ArrayList<>();
    private Map<Integer, Map<Symbol, Integer>> lalrTransitions = new HashMap<>();
    
    // ACTION table: state -> terminal -> Action
    public static class Action {
        public enum Type { SHIFT, REDUCE, ACCEPT }
        public final Type type;
        public final Integer state; // for SHIFT
        public final Production reduceProd; // for REDUCE

        private Action(Type type, Integer state, Production prod) {
            this.type = type; this.state = state; this.reduceProd = prod;
        }
        

        public static Action shift(int s) { return new Action(Type.SHIFT, s, null); }
        public static Action reduce(Production p) { return new Action(Type.REDUCE, null, p); }
        public static Action accept() { return new Action(Type.ACCEPT, null, null); }
    }

    private final Map<Integer, Map<Symbol, Action>> action = new HashMap<>();
    private final Map<Integer, Map<Symbol, Integer>> gotoTable = new HashMap<>();
    private final List<String> conflicts = new ArrayList<>();
    private int initialState = 0;

    public LALR1Table(LR1Automaton automaton) {
        this.automaton = automaton;
    }

    /**
     * Builds the LALR(1) parsing table.
     * 
     * This is a multi-step process.
     * 
     * Step 1: Ensure the underlying LR(1) automaton is built.
     *  automaton.build();
     * 
     * Step 2: Merge LR(1) states to create LALR(1) states.
     *  a. Group LR(1) states that have the same "kernel" (the set of LR(0) items).
     *      - A kernel item is an LR(1) item without its lookahead.
     *      - Create a map from a kernel (Set<KernelEntry>) to a list of state IDs that share that kernel.
     *  b. For each group of states with the same kernel:
     *      - Create a single new LALR(1) state.
     *      - This new state is formed by merging the LR(1) items from all states in the group.
     *      - Merging means for each kernel item, the new lookahead set is the union of all lookaheads for that item across the group.
     *      - Store these new LALR states in `lalrStates`.
     *  c. Create a mapping from old LR(1) state IDs to new LALR(1) state IDs.
     * 
     * Step 3: Build the transitions for the new LALR(1) automaton.
     *      - For each transition in the original LR(1) automaton `s -X-> t`:
     *      - Add a new transition for the LALR automaton: `merged(s) -X-> merged(t)`.
     *      - Use the mapping from step 2c to find the merged state IDs.
     *      - Store these new transitions in `lalrTransitions`.
     *  Step 4: Fill the ACTION and GOTO tables based on the LALR automaton.
     *      - Call a helper method, e.g., `fillActionGoto()`.
     */
    public void build(){
        // This is a multi-step process.
        // Step 1: Ensure the underlying LR(1) automaton is built.
        automaton.build();
        

        // Step 2: Merge LR(1) states to create LALR(1) states.
        //  a. Group LR(1) states that have the same "kernel" (the set of LR(0) items).
        //     - A kernel item is an LR(1) item without its lookahead.
        //     - Create a map from a kernel (Set<KernelEntry>) to a list of state IDs that share that kernel.
        HashMap<Set<KernelEntry>, List<Integer>> kernelStatesMap = new HashMap<>();

        for (int s = 0; s < this.automaton.getStates().size(); s++){
            //Obtain the LR1 state
            Set<LR1Item> stateLR1 = automaton.getStates().get(s);
            //We need to build a new kernelEntry by each item and add it to the set.
            Set<KernelEntry> kernelState = new HashSet<>();

            for (LR1Item lr1Item : stateLR1){
                //builing kernel entry, and adding to the set.
                kernelState.add(new KernelEntry(lr1Item.production, lr1Item.dotPosition));
            }

            //KernelStates is our key and we need to assign it a value, in this case a State with the same kernel.
            kernelStatesMap.computeIfAbsent(kernelState, k -> new LinkedList<>()).add(s);
        }


        //  b. For each group of states with the same kernel:
        //     - Create a single new LALR(1) state.
        //     - This new state is formed by merging the LR(1) items from all states in the group.
        //     - Merging means for each kernel item, the new lookahead set is the union of all lookaheads for that item across the group.
        //     - Store these new LALR states in `lalrStates`.

        //for each entry in the map
        for (Map.Entry<Set<KernelEntry>, List<Integer>> kernelStateEntry : kernelStatesMap.entrySet()){
            //we need to obtain the kernel, then obtain its state id list.
            List<Integer> listId = kernelStateEntry.getValue();
 
            //Helper map to get all merged lookaheads.
            Map<KernelEntry, Set<Symbol>> mergedLookaheads = new HashMap<>();
            
            //Using a for, we need to obtain all lookaheads.
            for ( Integer num : listId ){
                //get the current state
                Set<LR1Item> conjuntoItems = this.automaton.getStates().get(num);
                
                //For each item in the state.
                for ( LR1Item item : conjuntoItems ){
                    //por cada item, agrego su llave (KernelEntry) y su lookahead
                    KernelEntry key = new KernelEntry(item.production, item.dotPosition);
                    mergedLookaheads.computeIfAbsent(key, k -> new HashSet<>()).add(item.lookahead);
                    //So in this way. if items have diferents states but share kernel, we agroup all
                    //theirs lookahead using map.
                }
            }

            //We need to build all LALR1 states.
            Set<LR1Item> lalrState = new HashSet<>();
            for( Map.Entry<KernelEntry, Set<Symbol>> entryMerge : mergedLookaheads.entrySet() ){
                //obtain kernel entry which share lookahead.
                KernelEntry kernelCommon = entryMerge.getKey();
                //Getting all lookahead wich share a same kernel.
                Set<Symbol> lookaheads = entryMerge.getValue();
                //for each lookahead we need to create a new LR1 item.S
                for (Symbol look : lookaheads){
                    //building and adding a new LR1 item.
                    lalrState.add(new LR1Item(kernelCommon.production, kernelCommon.dotPosition, look));
                }
            }

            // Adding the new LALR1 state to the lalrStates.
            this.lalrStates.add(lalrState);
        }

        //  c. Create a mapping from old LR(1) state IDs to new LALR(1) state IDs.       
        //Helper Map.
        Map<Integer,Integer> oldStateToNewState = new HashMap<>();
        //Helper set.
        Set<LR1Item> gotten; int oldIndex,newIndex;
        //For each state in the automaton.
        for( oldIndex = 0; oldIndex<this.automaton.getStates().size(); oldIndex++ ){
            //obtain set of all items in that state.
            gotten = this.automaton.getStates().get(oldIndex);
            //For each lalrState
            for ( newIndex = 0; newIndex < this.lalrStates.size(); newIndex++) {
                //if current lalrstate contains all items that means this id state belongs to the lalrstate.
                if( this.lalrStates.get(newIndex).containsAll(gotten) ){
                    //Using the helper map, we put old id state as key and
                    //put new index state as value.
                    oldStateToNewState.put(oldIndex, newIndex);
                    System.out.println("OLD STATE: "+oldIndex+" NEWSTATE: "+newIndex);
                }
            }
        }

        //We need to update the reference to the initial state in the table.
        this.initialState=oldStateToNewState.get(0);
        System.out.println("Nuevo estado inicial"+this.initialState);

        // Step 3: Build the transitions for the new LALR(1) automaton.
        //  - For each transition in the original LR(1) automaton `s -X-> t`:
        //  - Add a new transition for the LALR automaton: `merged(s) -X-> merged(t)`.
        //  - Use the mapping from step 2c to find the merged state IDs.
        //  - Store these new transitions in `lalrTransitions`.
        
        //Helper vars.
        Symbol tranSymbol;
        int leftIndex,rightIndex;

        //  - For each transition in the original LR(1) automaton `s -X-> t`:
        for ( Map.Entry<Integer,Map<Symbol,Integer>> entryOriginSymbolDestiny : this.automaton.getTransitions().entrySet() ) {
            leftIndex = oldStateToNewState.get(entryOriginSymbolDestiny.getKey());
            
            for( Map.Entry<Symbol,Integer> entrySymbolDestiny : entryOriginSymbolDestiny.getValue().entrySet() ){
                //  - Add a new transition for the LALR automaton: `merged(s) -X-> merged(t)`.
                tranSymbol = entrySymbolDestiny.getKey();
                
                //  - Use the mapping from step 2c to find the merged state IDs.
                rightIndex = oldStateToNewState.get(entrySymbolDestiny.getValue());

                //  - Store these new transitions in `lalrTransitions`.
                this.lalrTransitions.computeIfAbsent( leftIndex , k -> new HashMap<>() ).put(tranSymbol , rightIndex);
            }
        }
        

        // Step 4: Fill the ACTION and GOTO tables based on the LALR automaton.
        //  - Call a helper method, e.g., `fillActionGoto()`.
        this.fillActionGoto();

    }

    /**
     * Auxiliar method to compute GoTo and Reduce values into the table
     * 
     * 1. Clear the action, gotoTable, and conflicts lists.
     * 2. Iterate through each LALR state `s` from 0 to lalrStates.size() - 1.
     * 3. For each state `s`, iterate through its LR1Item `it`.
     *     a. Get the symbol after the dot, `X = it.getSymbolAfterDot()`.
     *     b. If `X` is a terminal (SHIFT action):
     *        - Find the destination state `t` from `lalrTransitions.get(s).get(X)`.
     *        - Check for conflicts: if action table already has an entry for `[s, X]`, it's a conflict.
     *        - Otherwise, set `action[s][X] = SHIFT(t)`.
     *     c. If the dot is at the end of the production (`X` is null) (REDUCE or ACCEPT action):
     *        - This is an item like `[A -> α •, a]`.
     *        - If it's the augmented start production (`S' -> S •`) and lookahead is `$`, this is an ACCEPT action.
     *          - Set `action[s][$] = ACCEPT`.
     *        - Otherwise, it's a REDUCE action.
     *          - For the lookahead symbol `a` in the item:
     *          - Check for conflicts: if `action[s][a]` is already filled, report a Shift/Reduce or Reduce/Reduce conflict.
     *          - Otherwise, set `action[s][a] = REDUCE(A -> α)`.
     *  4. Populate the GOTO table.
     *     - For each state `s`, look at its transitions in `lalrTransitions`.
     *     - For each transition on a NON-TERMINAL symbol `B` to state `t`:
     *     - Set `gotoTable[s][B] = t`.
     */
    private void fillActionGoto() {
        // 1. Clear the action, gotoTable, and conflicts lists.
        action.clear();
        gotoTable.clear();
        conflicts.clear();

        // 2. Iterate through each LALR state `s` from 0 to lalrStates.size() - 1.
        for (int s=0;s<=lalrStates.size()-1;s++){
            // 3. For each state `s`, iterate through its LR1Item `it`.
            Set<LR1Item> state = lalrStates.get(s);

            for (LR1Item item : state){
                //    a. Get the symbol after the dot, `X = it.getSymbolAfterDot()`.
                Symbol x = item.getSymbolAfterDot();

                //    b. If `X` is a terminal (SHIFT action):
                if (x!=null && x.type==SymbolType.TERMINAL){
                    //- Find the destination state `t` from `lalrTransitions.get(s).get(X)`.
                    Integer t = null;
                    if (lalrTransitions.containsKey(s)) {
                        t = lalrTransitions.get(s).get(x);
                    }

                    //If there are not transition, just continue.
                    if (t == null) continue;

                    //- Check for conflicts: if action table already has an entry for `[s, X]`, it's a conflict.
                    Map<Symbol, Action> row = action.computeIfAbsent(s, k -> new HashMap<>());

                    //Verify if exist a transition with symbol x
                    if (row.containsKey(x)) {
                        //If it exist, then there is a conflict.
                        conflicts.add("Conflict in state: " +s+ " on terminal: " +x);
                        //If it exist and it is a REDUCE, and action incoming is a SHIFT, we replace it.
                        if(row.get(x).type==Action.Type.REDUCE ){
                            row.put(x, Action.shift(t));
                        }
                    }else {
                        //- Otherwise, set `action[s][X] = SHIFT(t)`.
                        row.put(x, Action.shift(t));
                    }   
                }

                if (x==null) {
                  
                    //To verify if action already contains an element, if not then create a empty Map.
                    Map<Symbol, Action> row = action.computeIfAbsent(s, k -> new HashMap<>());

                    //We need to compare augmented production and lookahead $ to get back an accept action.
                    if ( item.production.equals(this.automaton.getAugmentedProduction()) &&  item.lookahead.equals(this.automaton.dollar)){
                        //- Set `action[s][$] = ACCEPT`.
                        row.put(this.automaton.dollar, Action.accept());

                    }else{
                        //       - Otherwise, it's a REDUCE action.
                        //         - For the lookahead symbol `a` in the item:
                        //         - Check for conflicts: if `action[s][a]` is already filled, report a Shift/Reduce or Reduce/Reduce conflict.
                        if (row.containsKey(item.lookahead)){
                            //We need to report the conflict, and do nothing else cause if we has a reduce and in the table
                            // there is an shift action, is better stay table in that way.
                            Action existing = row.get(item.lookahead);
                            conflicts.add("Conflict in state " + s + " on lookahead " + item.lookahead +
                                      " between " + existing.type + " and REDUCE(" + item.production + ")");
                            
                        }else{
                            //- Otherwise, set `action[s][a] = REDUCE(A -> α)`.
                            row.put(item.lookahead, Action.reduce(item.production));
                        }
                    }
                }
            }
        }

        // 4. Populate the GOTO table.
        //    - For each state `s`, look at its transitions in `lalrTransitions`.
            for (int s=0;s<=lalrStates.size()-1;s++){
                //Getting al tanstitions in lalrstate.
                Map<Symbol, Integer> transitions = lalrTransitions.get(s);
                
                //if there are no transitions, continue next iteration.
                if (transitions == null) continue;

                //If already exist an map for this key use it, if not then create a empty map.
                Map<Symbol, Integer> gotoRow = gotoTable.computeIfAbsent(s, k -> new HashMap<>());

                //- For each transition on a NON-TERMINAL symbol `B` to state `t`:
                for (Map.Entry<Symbol, Integer> entry : transitions.entrySet()){
                    //Helper vars.
                    Symbol symbol = entry.getKey();
                    Integer t = entry.getValue();
                    
                    //If key is a no terminal symbol.
                    if (symbol.type == SymbolType.NON_TERMINAL) {
                        //    - Set `gotoTable[s][B] = t`.
                        //Populate goto table
                        gotoRow.put(symbol, t);
                    }
                }
                
            }
    }
    
    // ... (Getters and KernelEntry class can remain as is)
    public Map<Integer, Map<Symbol, Action>> getActionTable() { return action; }
    public Map<Integer, Map<Symbol, Integer>> getGotoTable() { return gotoTable; }
    public List<String> getConflicts() { return conflicts; }
    private static class KernelEntry {
        public final Production production;
        public final int dotPosition;
        KernelEntry(Production production, int dotPosition) {
            this.production = production;
            this.dotPosition = dotPosition;
        }
        @Override
        public boolean equals(Object obj) {
            if (this == obj) return true;
            if (!(obj instanceof KernelEntry)) return false;
            KernelEntry o = (KernelEntry) obj;
            return dotPosition == o.dotPosition && production.equals(o.production);
        }
        @Override
        public int hashCode() {
            int r = production.hashCode();
            r = 31 * r + dotPosition;
            return r;
        }
    }
    public List<Set<LR1Item>> getLALRStates() { return lalrStates; }
    public Map<Integer, Map<Symbol, Integer>> getLALRTransitions() { return lalrTransitions; }
    public int getInitialState() { return initialState; }
}
