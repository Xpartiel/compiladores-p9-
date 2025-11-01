package com.compiler.parser.lr;

import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.Stack;

import com.compiler.lexer.Token;
import com.compiler.parser.grammar.Production;
import com.compiler.parser.grammar.Symbol;
import com.compiler.parser.lr.LALR1Table.Action;
import com.compiler.parser.lr.LALR1Table.Action.Type;

/**
 * Implements the LALR(1) parsing engine.
 * Uses a stack and the LALR(1) table to process a sequence of tokens.
 * Complementary task for Practice 9.
 */
public class LALR1Parser {
    private final LALR1Table table;

    public LALR1Parser(LALR1Table table) {
        this.table = table;
    }

   // package-private accessor for tests
   LALR1Table getTable() {
       return table;
   }

   /**
    * Parses a sequence of tokens using the LALR(1) parsing algorithm.
    * @param tokens The list of tokens from the lexer.
    * @return true if the sequence is accepted, false if a syntax error is found.
    */
   public boolean parse(List<Token> tokens) {
        // 1. Initialize a stack for states and push the initial state (from table.getInitialState()).
        Stack<Integer> pila = new Stack<>();
        pila.push(this.table.getInitialState());
        
        // 2. Create a mutable list of input tokens from the parameter and add the end-of-input token ("$").
        List<Token> tokenList = new ArrayList<>(tokens);

        //Before add a new token $ to the list, we need to build it.
        Token dollar = new Token("$", "$");

        tokenList.add(dollar);

        // 3. Initialize an instruction pointer `ip` to 0, pointing to the first token.
        int ip = 0;

        // 4. Start a loop that runs until an ACCEPT or ERROR condition is met.
        //    a. Get the current state from the top of the stack.
        //    b. Get the current token `a` from the input list at index `ip`.
        //    c. Look up the action in the ACTION table: action = table.getActionTable()[state][a.type].
        //    d. If no action is found (it's null), it's a syntax error. Return false.
        //    e. If the action is SHIFT(s'):
        //       i. Push the new state s' onto the stack.
        //       ii. Advance the input pointer: ip++.
        //    f. If the action is REDUCE(A -> β):
        //       i. Pop |β| symbols (and states) from the stack. Handle epsilon productions (where |β|=0).
        //       ii. Get the new state `s` from the top of the stack.
        //       iii. Look up the GOTO state: goto_state = table.getGotoTable()[s][A].
        //       iv. If no GOTO state is found, it's an error. Return false.
        //       v. Push the goto_state onto the stack.
        //    g. If the action is ACCEPT:
        //       i. The input has been parsed successfully. Return true.
        //    h. If the action is none of the above, it's an unhandled case or error. Return false.

        // 4. Start a loop that runs until an ACCEPT or ERROR condition is met.
        //Se refiere a que tengo que hacer un algoritmo de punto fijo?
        int idState = -1;
        Action action;
        while(true){
            //fix: initialize action as null in each iteration.
            action=null;
            //a. Get the current state from the top of the stack.
            idState = pila.peek();

            //b. Get the current token `a` from the input list at index `ip`.
            Token a = tokenList.get(ip);

            //c. Look up the action in the ACTION table: action = table.getActionTable()[state][a.type].
            Map<Symbol, Action> keyIdState=table.getActionTable().get(idState);
            
            //We look for the lookahead symbol.
            Symbol lookupSymbol = null;
            //For each key in the map.
            for (Symbol s : keyIdState.keySet()) {
                //if symbol and a has the same name.
                if (s.name.equals(a.type)) {
                    //we have found the lookahead symbol
                    lookupSymbol = s;
                    break;
                }
            }

            //if we have not found any match with a.type then lookup is null-
            if (lookupSymbol != null) {
                //if not null, then we need to obtian its action.
                action = keyIdState.get(lookupSymbol);
            }
            //d. If no action is found (it's null), it's a syntax error. Return false.
            if(action==null){
                //Syntax error, there is no action in this state.
                return false;
            }

            //e. If the action is SHIFT(s'):
            if (action.type == Type.SHIFT){
                //i. Push the new state s' onto the stack.
                pila.push(action.state);
                //ii. Advance the input pointer: ip++.
                ip++;
            }else
            //    f. If the action is REDUCE(A -> β):
            if (action.type == Type.REDUCE){
                //i. Pop |β| symbols (and states) from the stack. Handle epsilon productions (where |β|=0).

                //Getting the action production.
                Production prod = action.reduceProd;
                //Helper var to save the size of Beta.
                int sizeB;
                //epsilon transition handler
                if(prod.getRight().size()==1 && prod.getRight().get(0).name.equals("epsilon")){
                    sizeB=0;
                }else{
                    //saving size of Beta.
                    sizeB = prod.getRight().size();
                }
                
                //Make a pop a size of Beta times.
                for (int i = 0; i <sizeB; i++){
                    pila.pop();
                }
                

                //ii. Get the new state `s` from the top of the stack.
                int newS;
                if( !pila.isEmpty() ){
                    newS = pila.peek();
                }else{
                    return false;
                }
                
                //iii. Look up the GOTO state: goto_state = table.getGotoTable()[s][A].
                //helper var
                Integer goto_state =null; 
                Map<Symbol, Integer> newSToSymbolIntMap=table.getGotoTable().get(newS);
                if (newSToSymbolIntMap != null){
                    goto_state = newSToSymbolIntMap.get(prod.getLeft());
                    
                }
                //iv. If no GOTO state is found, it's an error. Return false.
                if (goto_state==null){
                    return false;
                }else{
                    //v. Push the goto_state onto the stack.
                    pila.push(goto_state);
                } 
            }else
            //g. If the action is ACCEPT:     
            if (action.type==Type.ACCEPT){
            //i. The input has been parsed successfully. Return true.    
                return true;
            }else{
                //    h. If the action is none of the above, it's an unhandled case or error. Return false.
                return false;
            }
            
        }
   }
}
