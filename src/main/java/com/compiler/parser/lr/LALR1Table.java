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
     */
    public void build(){
        // This is a multi-step process.
        // Step 1: Ensure the underlying LR(1) automaton is built.
        automaton.build();
        //automaton.getStates();
        

        // Step 2: Merge LR(1) states to create LALR(1) states.
        //  a. Group LR(1) states that have the same "kernel" (the set of LR(0) items).
        //     - A kernel item is an LR(1) item without its lookahead.
        //     - Create a map from a kernel (Set<KernelEntry>) to a list of state IDs that share that kernel.
        /*
         * CREAR UN MAPEO QUE RECIBA UN kernel entry, y devuelva una lista de id de estados
         * que compartan dicho kernel.
         * 
         * por cada estado, debo agregar su kernel al mapeo (usa computeIfAbsent para crear la lista)
         * como llave, y en el valor (lista) debo agregar el id del estado.
         * 
         * Esto quiere decir que vpy a ocupar el indice del for, por tanto no puedo usar for each.
         * De momento queda en duda porque queremos un set de kernel entry. 
         * 
         */
        
        HashMap<Set<KernelEntry>, List<Integer>> kernelStatesMap = new HashMap<>();


        for (int s = 0; s < this.automaton.getStates().size(); s++){
            //Obtengo el estado LR1
            Set<LR1Item> stateLR1=automaton.getStates().get(s);
            //necesito crear un kernel entry por cada item y agregarlo al conjunto.
            Set<KernelEntry> kernelStates = new HashSet<>();

            for (LR1Item lr1Item : stateLR1){
                //Creo el kernel entry y lo agrego al conjunto
                kernelStates.add(new KernelEntry(lr1Item.production, lr1Item.dotPosition));                
            }

            //Agregamos el conjunto kernelStates como llave y le asignamos un valor.
            kernelStatesMap.computeIfAbsent(kernelStates, k -> new LinkedList<>()).add(s);
        }


        //  b. For each group of states with the same kernel:
        //     - Create a single new LALR(1) state.
        //     - This new state is formed by merging the LR(1) items from all states in the group.
        //     - Merging means for each kernel item, the new lookahead set is the union of all lookaheads for that item across the group.
        //     - Store these new LALR states in `lalrStates`.

        /**
         * Creamos un nuevo LALR(1) estado (un estado LALR1 es un conjunto de items de LR1), 
         * para ello debemos iterar sobre los valores del diccionario KeyEntryStateMap
         * obtener la lista de todos los elementos que comparten un kernel (es decir, el valor de 
         * cada llave en el diccionario).
         * Luego con dicha lista debemos obtener todos los item de los id de los estados contenidos
         * dicha lista, y agregar todos esos item a un conjunto.
         * 
         * Por ultimo solo debemos agregar el nuevo estado LALR1 a la lista de estados LALR1.
         */


        //  c. Create a mapping from old LR(1) state IDs to new LALR(1) state IDs.


        // Step 3: Build the transitions for the new LALR(1) automaton.
        //  - For each transition in the original LR(1) automaton `s -X-> t`:
        //  - Add a new transition for the LALR automaton: `merged(s) -X-> merged(t)`.
        //  - Use the mapping from step 2c to find the merged state IDs.
        //  - Store these new transitions in `lalrTransitions`.

        // Step 4: Fill the ACTION and GOTO tables based on the LALR automaton.
        //  - Call a helper method, e.g., `fillActionGoto()`.






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

                    //Si no hay transición, simplemente continúa
                    if (t == null) continue;

                    //- Check for conflicts: if action table already has an entry for `[s, X]`, it's a conflict.
                    //Asegurar que la fila de acciones para este estado exista
                    Map<Symbol, Action> row = action.computeIfAbsent(s, k -> new HashMap<>());

                    //Verificamos que exista una transicion con x
                    if (row.containsKey(x)) {
                        //si existe, entonces hay un conflicto.
                        conflicts.add("Conflict in state: " +s+ " on terminal: " +x);
                    }else {
                        //- Otherwise, set `action[s][X] = SHIFT(t)`.
                        row.put(x, Action.shift(t));
                    }   
                }

                //    c. If the dot is at the end of the production (`X` is null) (REDUCE or ACCEPT action):
                //       - This is an item like `[A -> α •, a]`.
                //       - If it's the augmented start production (`S' -> S •`) and lookahead is `$`, this is an ACCEPT action.
                //         - Set `action[s][$] = ACCEPT`.
                //       - Otherwise, it's a REDUCE action.
                //         - For the lookahead symbol `a` in the item:
                //         - Check for conflicts: if `action[s][a]` is already filled, report a Shift/Reduce or Reduce/Reduce conflict.
                //         - Otherwise, set `action[s][a] = REDUCE(A -> α)`.
                if (x==null) {
                    //Obtener el string de S'
                    String sPrime = this.automaton.getAugmentedLeftName();
                    //obtener el simbolo S'
                    Symbol initialSymbolPrime = new Symbol(sPrime, SymbolType.NON_TERMINAL);
                    //obtener el simbolo S
                    int index= sPrime.indexOf("'");
                    String sInitial= sPrime.substring(0,index);
                    //crear el simbolo.
                    Symbol sSymbol = new Symbol(sInitial, SymbolType.NON_TERMINAL);

                    //Ahora hay que construir la produccion.
                    //S'-> S
                    Production prod = new Production(initialSymbolPrime, List.of(sSymbol));

                    //Para verificar si el action ya contiene un elemento.
                    Map<Symbol, Action> row = action.computeIfAbsent(s, k -> new HashMap<>());

                    if (item.production.equals(prod)&& item.lookahead.equals(this.automaton.dollar)){
                        //Si la produccion es del tipo S' -> S y el lookahead es "$", aceptamos.
                        //- Set `action[s][$] = ACCEPT`.
                        row.put(this.automaton.dollar, Action.accept());
                    }else{
                        //       - Otherwise, it's a REDUCE action.
                        //         - For the lookahead symbol `a` in the item:
                        //         - Check for conflicts: if `action[s][a]` is already filled, report a Shift/Reduce or Reduce/Reduce conflict.
                        if (row.containsKey(item.lookahead)){
                            //reportar el conflicto.
                            Action existing = row.get(item.lookahead);
                            conflicts.add("Conflict in state " + s + " on lookahead " + item.lookahead +
                                      " between " + existing.type + " and REDUCE(" + item.production + ")");
                        }else{
                            //         - Otherwise, set `action[s][a] = REDUCE(A -> α)`.
                            row.put(item.lookahead, Action.reduce(item.production));
                        }
                    }
                }
            }
        }
        //Aqui va el paso 4.
        // 4. Populate the GOTO table.
        //    - For each state `s`, look at its transitions in `lalrTransitions`.
        //Para cada estado, tengo que revisar sus lalrtransiciones.
            for (int s=0;s<=lalrStates.size()-1;s++){
                //Obtengo las transiciones del estado.
                Map<Symbol, Integer> transitions = lalrTransitions.get(s);
                //Si no hay transiciones, continua.
                if (transitions == null) continue;

                //Nos aseguramos de que haya un mapeo para el valor de la llave
                Map<Symbol, Integer> gotoRow = gotoTable.computeIfAbsent(s, k -> new HashMap<>());

                //- For each transition on a NON-TERMINAL symbol `B` to state `t`:
                //Para cada transicion, reviso cuales son no terminales.
                for (Map.Entry<Symbol, Integer> entry : transitions.entrySet()){
                    Symbol symbol = entry.getKey();
                    Integer t = entry.getValue();
                    
                    //si la llave es un simbolo no terminal.
                    if (symbol.type == SymbolType.NON_TERMINAL) {
                        //    - Set `gotoTable[s][B] = t`.
                        //poblamos la tabla del goto.
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
