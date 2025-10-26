package com.compiler.lexer;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Portable representation of a DFA as a transition table.
 */
public class LexerDefinition {
    public final List<Character> alphabet; // index -> char
    public final int startState; // start state index
    public final int[][] transitions; // [state][alphaIndex] -> nextState (or -1)
    public final boolean[] isFinal; // state -> is final
    public final String[] tokenTypeNames; // state -> token name or null

    public LexerDefinition(List<Character> alphabet, int startState, int[][] transitions, boolean[] isFinal, String[] tokenTypeNames) {
        this.alphabet = alphabet;
        this.startState = startState;
        this.transitions = transitions;
        this.isFinal = isFinal;
        this.tokenTypeNames = tokenTypeNames;
    }

    /**
     * Finds the alphabet index for the given character, or -1 if not present.
     */
    public int alphabetIndex(char c) {
        for (int i = 0; i < alphabet.size(); i++) if (alphabet.get(i) == c) return i;
        return -1;
    }

    /**
     * Serialize this LexerDefinition to a JSON string.
     */
    public String toJson() {
        StringBuilder sb = new StringBuilder();
        sb.append('{');
        // alphabet
        sb.append("\"alphabet\":[");
        for (int i = 0; i < alphabet.size(); i++) {
            if (i > 0) sb.append(',');
            char c = alphabet.get(i);
            sb.append('"');
            // switch (c) {
            //     case '\\' -> sb.append("\\\\");
            //     case '"' -> sb.append("\\\"");
            //     default -> sb.append(c);
            // }
            switch (c) {
                case '\\':
                    sb.append("\\\\");
                    break;
                case '"':
                    sb.append("\\\"");
                    break;
                default:
                    sb.append(c);
                    break;
            }
            

            sb.append('"');
        }
        sb.append(']');

        // startState
        sb.append(",\"startState\":").append(startState);

        // transitions
        sb.append(",\"transitions\":[");
        for (int i = 0; i < transitions.length; i++) {
            if (i > 0) sb.append(',');
            sb.append('[');
            for (int j = 0; j < transitions[i].length; j++) {
                if (j > 0) sb.append(',');
                sb.append(transitions[i][j]);
            }
            sb.append(']');
        }
        sb.append(']');

        // isFinal
        sb.append(",\"isFinal\":[");
        for (int i = 0; i < isFinal.length; i++) {
            if (i > 0) sb.append(',');
            sb.append(isFinal[i] ? "true" : "false");
        }
        sb.append(']');

        // tokenTypeNames
        sb.append(",\"tokenTypeNames\":[");
        for (int i = 0; i < tokenTypeNames.length; i++) {
            if (i > 0) sb.append(',');
            String s = tokenTypeNames[i];
            if (s == null) sb.append("null");
            else {
                sb.append('"');
                sb.append(s.replace("\\", "\\\\").replace("\"", "\\\""));
                sb.append('"');
            }
        }
        sb.append(']');

        sb.append('}');
        return sb.toString();
    }

    /**
     * Save JSON representation to a file path.
     */
    public void saveToFile(String path) throws IOException {
        Files.writeString(Paths.get(path), toJson());
    }

    /**
     * Load a LexerDefinition from a JSON file previously produced by toJson().
     */
    public static LexerDefinition loadFromFile(String path) throws IOException {
        String s = Files.readString(Paths.get(path));
        return fromJson(s);
    }

    private static LexerDefinition fromJson(String s) {
        // remove whitespace that isn't inside strings for easier parsing
        // Since our serializer only emits simple strings without embedded spaces, this is safe enough.
        String compact = s.replaceAll("\\s+", "");

        // alphabet
        List<Character> alphabet = new ArrayList<>();
        Matcher mAlpha = Pattern.compile("\\\"alphabet\\\":\\[(.*?)\\]").matcher(compact);
        if (mAlpha.find()) {
            String body = mAlpha.group(1);
            Matcher m = Pattern.compile("\\\"(.*?)\\\"").matcher(body);
            while (m.find()) {
                String ch = m.group(1);
                char c = ch.length() > 0 ? ch.charAt(0) : '\0';
                alphabet.add(c);
            }
        }

        // startState
        Matcher mStart = Pattern.compile("\"startState\":(\\d+)").matcher(compact);
        int startState = 0;
        if (mStart.find()) startState = Integer.parseInt(mStart.group(1));

        // transitions: find all inner arrays
        Matcher mTransOuter = Pattern.compile("\\\"transitions\\\":\\[(.*)\\],\\\"isFinal\\\":").matcher(compact);
        List<int[]> transitionsList = new ArrayList<>();
        if (mTransOuter.find()) {
            String inner = mTransOuter.group(1);
            Matcher row = Pattern.compile("\\[(.*?)\\]").matcher(inner);
            while (row.find()) {
                String nums = row.group(1).trim();
                if (nums.isEmpty()) { transitionsList.add(new int[0]); continue; }
                String[] parts = nums.split(",");
                int[] r = new int[parts.length];
                for (int i = 0; i < parts.length; i++) r[i] = Integer.parseInt(parts[i].trim());
                transitionsList.add(r);
            }
        }

        int[][] transitions = transitionsList.toArray(int[][]::new);

        // isFinal
        Matcher mIs = Pattern.compile("\\\"isFinal\\\":\\[(.*?)\\],\\\"tokenTypeNames\\\":").matcher(compact);
        boolean[] isFinal = new boolean[transitions.length];
        if (mIs.find()) {
            String body = mIs.group(1);
            if (!body.isEmpty()) {
                String[] parts = body.split(",");
                for (int i = 0; i < parts.length && i < isFinal.length; i++) {
                    isFinal[i] = parts[i].trim().equals("true");
                }
            }
        }

        // tokenTypeNames
        Matcher mTok = Pattern.compile("\\\"tokenTypeNames\\\":\\[(.*?)\\]\\}?").matcher(compact);
        String[] tokenTypeNames = new String[transitions.length];
        if (mTok.find()) {
            String body = mTok.group(1);
            // split respecting null and quoted strings
            List<String> items = new ArrayList<>();
            int idx = 0;
            while (idx < body.length()) {
                if (body.startsWith("null", idx)) { items.add(null); idx += 4; }
                else if (body.charAt(idx) == '"') {
                    int end = body.indexOf('"', idx + 1);
                    while (end != -1 && body.charAt(end - 1) == '\\') {
                        end = body.indexOf('"', end + 1);
                    }
                    String raw = body.substring(idx + 1, end);
                    items.add(raw.replace("\\\"", "\"").replace("\\\\", "\\"));
                    idx = end + 1;
                } else idx++;
                if (idx < body.length() && body.charAt(idx) == ',') idx++;
            }
            for (int i = 0; i < items.size() && i < tokenTypeNames.length; i++) tokenTypeNames[i] = items.get(i);
        }

        // ensure arrays sizes match
        if (tokenTypeNames.length != transitions.length) tokenTypeNames = Arrays.copyOf(tokenTypeNames, transitions.length);

        return new LexerDefinition(alphabet, startState, transitions, isFinal, tokenTypeNames);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        LexerDefinition other = (LexerDefinition) o;
        if (this.startState != other.startState) return false;
        if (this.alphabet.size() != other.alphabet.size()) return false;
        for (int i = 0; i < alphabet.size(); i++) if (!this.alphabet.get(i).equals(other.alphabet.get(i))) return false;
        if (this.transitions.length != other.transitions.length) return false;
        for (int i = 0; i < transitions.length; i++) {
            if (this.transitions[i].length != other.transitions[i].length) return false;
            for (int j = 0; j < transitions[i].length; j++) if (this.transitions[i][j] != other.transitions[i][j]) return false;
        }
        if (this.isFinal.length != other.isFinal.length) return false;
        for (int i = 0; i < isFinal.length; i++) if (this.isFinal[i] != other.isFinal[i]) return false;
        if (this.tokenTypeNames.length != other.tokenTypeNames.length) return false;
        for (int i = 0; i < tokenTypeNames.length; i++) {
            String a = this.tokenTypeNames[i];
            String b = other.tokenTypeNames[i];
            if (a == null ? b != null : !a.equals(b)) return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        int result = Integer.hashCode(startState);
        result = 31 * result + alphabet.hashCode();
        result = 31 * result + Arrays.deepHashCode(transitions);
        result = 31 * result + Arrays.hashCode(isFinal);
        result = 31 * result + Arrays.hashCode(tokenTypeNames);
        return result;
    }
}
