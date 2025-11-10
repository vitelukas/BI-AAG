#ifndef __PROGTEST__
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <functional>
#include <iomanip>
#include <iostream>
#include <list>
#include <map>
#include <memory>
#include <numeric>
#include <optional>
#include <queue>
#include <random>
#include <set>
#include <sstream>
#include <stack>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <variant>
#include <vector>

#include "sample.h"
#endif
/* ======================================================================================================== */
using namespace std;

struct NFAState {
    uint8_t m_symbol;
    std::map<uint8_t, std::vector<std::weak_ptr<NFAState>>> transitions;
    bool isAccepting = false;
};

class NFA {
    private: 
        shared_ptr<NFAState> start;
        // keep track of all created states to manage their lifetime
        std::vector<std::shared_ptr<NFAState>> allStates;

        shared_ptr<NFAState> newState (uint8_t symbol = 0) {
            auto s = make_shared<NFAState>();
            s->m_symbol = symbol;
            s->isAccepting = false;
            allStates.push_back(s);
            return s;
        }

        // Helper recursive method - creates sets of start states and final states, creates the transitions map, checks if nodes contain ε
        // Returns true if the given node of regular expression contains ε
        bool buildRec(
            const regexp::RegExp &node,
            std::vector<std::shared_ptr<NFAState>> &starts,
            std::vector<std::shared_ptr<NFAState>> &finals,
            std::set<std::pair< shared_ptr<NFAState>, shared_ptr<NFAState> >> &neighbors
        ) {
            return std::visit(overloaded {
                // ∅
                [&](const std::unique_ptr<regexp::Empty>&arg) {
                    // doesn't contain ε;
                    return false;
                },
                // ε
                [&](const std::unique_ptr<regexp::Epsilon>&arg) {
                    // contains ε;
                    return true;
                },
                // a
                [&](const std::unique_ptr<regexp::Symbol>& sym) {
                    auto s = newState(sym->m_symbol);
                    // and individual symbol is both start and final state
                    starts.push_back(s);
                    finals.push_back(s);
                    // doesn't contain ε;
                    return false;
                },
                // a + b
                [&](const std::unique_ptr<regexp::Alternation>& alt) {
                    // starts, finals, neighbors of an alternation
                    //is a union of starts, finals, neighbors of both sides
                    bool lContainsEps = buildRec(alt->m_left, starts, finals, neighbors);
                    bool rContainsEps = buildRec(alt->m_right, starts, finals, neighbors);
                    
                    // contains ε if at least one of the side of the alternation contains ε
                    return (lContainsEps || rContainsEps);
                },
                // a . b
                [&](const std::unique_ptr<regexp::Concatenation>& cat) {       
                    // keeping interim results,
                    // so that we can correctly implement the concatenation logic for starts, finals, neighbors            
                    std::vector<shared_ptr<NFAState>> leftStarts, leftFinals, rightStarts, rightFinals;
                    std::set<std::pair<shared_ptr<NFAState>, shared_ptr<NFAState>>> leftNeighbors, rightNeighbors;
                    bool lContainsEps = buildRec(cat->m_left, leftStarts, leftFinals, leftNeighbors);
                    bool rContainsEps = buildRec(cat->m_right, rightStarts, rightFinals, rightNeighbors);
                    
                    // starts of Concatenation = starts of left side
                    //  + (if left side contains ε then also starts of right side)
                    starts.insert(starts.end(), leftStarts.begin(), leftStarts.end());
                    if (lContainsEps)
                        starts.insert(starts.end(), rightStarts.begin(), rightStarts.end());

                    // finals of Concatenation = similar to starts but mirrored
                    finals.insert(finals.end(), rightFinals.begin(), rightFinals.end());
                    if (rContainsEps)
                        finals.insert(finals.end(), leftFinals.begin(), leftFinals.end());

                    // neighbors of Concatenation = neighbors of both sides
                    //  + new neighbors created by connecting finals of left side to starts of right side
                    neighbors.insert(leftNeighbors.begin(), leftNeighbors.end());
                    neighbors.insert(rightNeighbors.begin(), rightNeighbors.end());
                    for (const auto &leftFinal : leftFinals) {
                        for (const auto &rightStart : rightStarts) {
                            neighbors.emplace(move(leftFinal), move(rightStart));
                        }
                    }                            

                    // contains ε if both sides of the concatenation contain ε
                    return (lContainsEps && rContainsEps);
                },
                // a*
                [&](const std::unique_ptr<regexp::Iteration>& it) {
                    // starts and finals
                    std::vector<std::shared_ptr<NFAState>> nodeStarts;
                    std::vector<std::shared_ptr<NFAState>> nodeFinals;
                    buildRec(it->m_node, nodeStarts, nodeFinals, neighbors);
                    // neighbors of Iteration = nighbors of the inner node
                    //  + new neighbors created by connecting finals to starts of te inner node
                    for (const auto &nodeFinal : nodeFinals) {
                        for (const auto &nodeStart : nodeStarts) {
                            neighbors.emplace(move(nodeFinal), move(nodeStart));
                        }
                    }
                    starts.insert(starts.end(), nodeStarts.begin(), nodeStarts.end());
                    finals.insert(finals.end(), nodeFinals.begin(), nodeFinals.end());
                    
                    // contains ε
                    return true;
                },
                [](auto) { return false; }
            }, node);
        }

    public:
        NFA (void) = default;
        ~NFA (void) = default;

        // Build an NFA from a given reg. expression using the Glushkov's neighbors method
        void buildFromRegexp (const regexp::RegExp &re) {
            // create a start state
            start = newState('q');
            std::vector<shared_ptr<NFAState>> startStates, finalStates;
            std::set<std::pair<shared_ptr<NFAState>, shared_ptr<NFAState>>> neighbors;
            bool regexpContainsEps = buildRec(re, startStates, finalStates, neighbors);
            
            // add a transition from the new start state to all the start states of the reg. expression
            for (auto &s : startStates)
                start->transitions[s->m_symbol].push_back(s);
            for (auto &f : finalStates)
                f->isAccepting = true;
            // add transition for all the neighbors, where the transition is from the left neigh
            //  to the right neigh, using the symbol of the right neigh
            for (auto &neighborsPair : neighbors) {
                auto &leftNeighbor = neighborsPair.first;
                auto &rightNeighbor = neighborsPair.second;
                leftNeighbor->transitions[rightNeighbor->m_symbol].push_back(rightNeighbor);
            }
            // if the original reg. expression accepted ε as an input 
            //  => make the new start state also a final(accepting) state so that the NFA accepts ε
            if (regexpContainsEps)
                start->isAccepting = true;
        }
        
        // use a customized BFS to traverse the created NFA and check if it accepts the given word
        bool accepts (const Word &word) {
            std::unordered_set<shared_ptr<NFAState>> current, next;
            current.insert(start);
            
            // try process all the chars in the given word
            for (auto c : word) {
                next.clear();
                // check all states in the set of current states
                for (auto &state : current) {
                    auto it = state->transitions.find(c);
                    // if the state contains at least one transition to another state,
                    //  using the c for transition
                    if (it != state->transitions.end()) {
                        // iterate over all of the possible transitions
                        for (auto &nxtState : it->second) {
                            if(auto sharedPointer = nxtState.lock())
                                // add the state from the possible transition into
                                //  a set of states which will be visited next
                                next.insert(sharedPointer);
                        }
                    }
                }
                // we haven't read the whole word yet and we have no more states to go to
                if (next.empty())
                    return false;

                current = next;
            }
            
            // we have read the whole word and one of the states we are currently in, is a final(~accepting) state
            for (auto &state : current) {
                if (state->isAccepting)
                    return true;
            }
            
            // we have read the whole word but we have no more viable states to go to
            return false;
        }
};

// A light simplification of the reg. expression for an easier work during the building process of the nfa
regexp::RegExp simplifyRegexp(const regexp::RegExp &re) {
    return std::visit(overloaded {
        [](const std::unique_ptr<regexp::Empty> &) {
            return regexp::RegExp(std::make_unique<regexp::Empty>());
        },
        [](const std::unique_ptr<regexp::Epsilon> &) {
            return regexp::RegExp(std::make_unique<regexp::Epsilon>());
        },
        [](const std::unique_ptr<regexp::Symbol> &s) {
            return regexp::RegExp(std::make_unique<regexp::Symbol>(s->m_symbol));
        },
        [](const std::unique_ptr<regexp::Iteration> &it) -> regexp::RegExp {
            auto inner = simplifyRegexp(it->m_node);
            // ∅* = ε* = ε
            if (std::holds_alternative<std::unique_ptr<regexp::Empty>>(inner) ||
                std::holds_alternative<std::unique_ptr<regexp::Epsilon>>(inner))
                return regexp::RegExp(std::make_unique<regexp::Epsilon>());
            // (x*)* = x*
            if (std::holds_alternative<std::unique_ptr<regexp::Iteration>>(inner))
                return inner;
                
            return regexp::RegExp(std::make_unique<regexp::Iteration>(std::move(inner)));
        },
        [](const std::unique_ptr<regexp::Alternation> &alt) -> regexp::RegExp {
            auto left = simplifyRegexp(alt->m_left);
            auto right = simplifyRegexp(alt->m_right);
            // x + ∅ = x, ∅ + x = x
            if (std::holds_alternative<std::unique_ptr<regexp::Empty>>(left))
                return right;
            if (std::holds_alternative<std::unique_ptr<regexp::Empty>>(right))
                return left;
            // x + x = x
            if (regexp::print(left) == regexp::print(right))
                return left;

            return regexp::RegExp(std::make_unique<regexp::Alternation>(std::move(left), std::move(right)));
        },
        [](const std::unique_ptr<regexp::Concatenation> &cat) -> regexp::RegExp {
            auto left = simplifyRegexp(cat->m_left);
            auto right = simplifyRegexp(cat->m_right);

            // x.∅ = ∅.x = ∅
            if (std::holds_alternative<std::unique_ptr<regexp::Empty>>(left) ||
                std::holds_alternative<std::unique_ptr<regexp::Empty>>(right))
                return regexp::RegExp(std::make_unique<regexp::Empty>());
            // ε.x = x, x.ε = x
            if (std::holds_alternative<std::unique_ptr<regexp::Epsilon>>(left))
                return right;
            if (std::holds_alternative<std::unique_ptr<regexp::Epsilon>>(right))
                return left;

            return regexp::RegExp(std::make_unique<regexp::Concatenation>(std::move(left), std::move(right)));
        }
    }, re);
}
/* ----------------------------------------------------------------- */

// For the given regular expression (represented as a tree) and list of words, return the set of indices of words that match the regular expression.
std::set<size_t> wordsMatch(const regexp::RegExp &regexp, const std::vector<Word> &words) {
    std::set<size_t> result = {};
    regexp::RegExp simplifiedRegexp = simplifyRegexp(regexp);
    NFA nfa;
    nfa.buildFromRegexp(simplifiedRegexp);

    for (size_t i = 0; i < words.size(); i++) {
        if (nfa.accepts(words[i]))
            result.insert(i);
    }

    return result;
}

/* ======================================================================================================== */
#ifndef __PROGTEST__
int main() {
    // basic test 1
    regexp::RegExp re1 = std::make_unique<regexp::Iteration>(
        std::make_unique<regexp::Concatenation>(
            std::make_unique<regexp::Concatenation>(
                std::make_unique<regexp::Concatenation>(
                    std::make_unique<regexp::Iteration>(
                        std::make_unique<regexp::Alternation>(
                            std::make_unique<regexp::Symbol>('a'),
                            std::make_unique<regexp::Symbol>('b'))),
                    std::make_unique<regexp::Symbol>('a')),
                std::make_unique<regexp::Symbol>('b')),
            std::make_unique<regexp::Iteration>(
                std::make_unique<regexp::Alternation>(
                    std::make_unique<regexp::Symbol>('a'),
                    std::make_unique<regexp::Symbol>('b')))));
    assert(wordsMatch(re1, {Word{}}) == std::set<size_t>{0});
    assert(wordsMatch(re1, {Word{'a', 'b'}}) == std::set<size_t>{0});
    assert(wordsMatch(re1, {Word{'a'}}) == std::set<size_t>{});
    assert(wordsMatch(re1, {Word{'a', 'a', 'a', 'a'}}) == std::set<size_t>{});
    assert(wordsMatch(re1, {Word{'a', 'a', 'a', 'c'}}) == std::set<size_t>{});
    assert(wordsMatch(re1, {Word{'a', 'a', 0x07, 'c'}}) == std::set<size_t>{});
    assert(wordsMatch(re1, {Word{'a', 'a', 'b'}}) == std::set<size_t>{0});
    assert(wordsMatch(re1, {Word{'a', 'a', 'b', 'a', 'a', 'b', 'a', 'a', 'b', 'a', 'a', 'b', 'a', 'a', 'b', 'a', 'a', 'b'}}) == std::set<size_t>{0});
    assert((wordsMatch(re1, {Word{}, Word{'a', 'b'}, Word{'a'}, Word{'a', 'a', 'a', 'a'}, Word{'a', 'a', 'a', 'c'}, Word{'a', 'a', 0x07, 'c'}, Word{'a', 'a', 'b'}, Word{'a', 'a', 'b', 'a', 'a', 'b', 'a', 'a', 'b', 'a', 'a', 'b', 'a', 'a', 'b', 'a', 'a', 'b'}}) == std::set<size_t>{0, 1, 6, 7}));

    // basic test 2
    regexp::RegExp re2 = std::make_unique<regexp::Concatenation>(
        std::make_unique<regexp::Concatenation>(
            std::make_unique<regexp::Iteration>(
                std::make_unique<regexp::Concatenation>(
                    std::make_unique<regexp::Concatenation>(
                        std::make_unique<regexp::Iteration>(
                            std::make_unique<regexp::Alternation>(
                                std::make_unique<regexp::Symbol>('a'),
                                std::make_unique<regexp::Symbol>('b'))),
                        std::make_unique<regexp::Iteration>(
                            std::make_unique<regexp::Alternation>(
                                std::make_unique<regexp::Symbol>('c'),
                                std::make_unique<regexp::Symbol>('d')))),
                    std::make_unique<regexp::Iteration>(
                        std::make_unique<regexp::Alternation>(
                            std::make_unique<regexp::Symbol>('e'),
                            std::make_unique<regexp::Symbol>('f'))))),
            std::make_unique<regexp::Empty>()),
        std::make_unique<regexp::Iteration>(
            std::make_unique<regexp::Alternation>(
                std::make_unique<regexp::Symbol>('a'),
                std::make_unique<regexp::Symbol>('b'))));
    assert(wordsMatch(re2, {Word{}}) == std::set<size_t>{});
    assert(wordsMatch(re2, {Word{'a', 'b'}}) == std::set<size_t>{});
    assert(wordsMatch(re2, {Word{'a', 'b', 'c', 'd'}}) == std::set<size_t>{});
    assert(wordsMatch(re2, {Word{'a', 'b', 'c', 'd', 'e', 'f'}}) == std::set<size_t>{});
    assert(wordsMatch(re2, {Word{'a', 'b', 'c', 'd', 'e', 'f', 'a', 'b'}}) == std::set<size_t>{});
    assert((wordsMatch(re2, {Word{}, Word{'a', 'b'}, Word{'a', 'b', 'c', 'd'}, Word{'a', 'b', 'c', 'd', 'e', 'f'}, Word{'a', 'b', 'c', 'd', 'e', 'f', 'a', 'b'}}) == std::set<size_t>{}));

    // basic test 3
    regexp::RegExp re3 = std::make_unique<regexp::Concatenation>(
        std::make_unique<regexp::Concatenation>(
            std::make_unique<regexp::Concatenation>(
                std::make_unique<regexp::Symbol>('0'),
                std::make_unique<regexp::Symbol>('1')),
            std::make_unique<regexp::Symbol>('1')),
        std::make_unique<regexp::Iteration>(
            std::make_unique<regexp::Alternation>(
                std::make_unique<regexp::Alternation>(
                    std::make_unique<regexp::Concatenation>(
                        std::make_unique<regexp::Concatenation>(
                            std::make_unique<regexp::Symbol>('0'),
                            std::make_unique<regexp::Symbol>('1')),
                        std::make_unique<regexp::Symbol>('1')),
                    std::make_unique<regexp::Concatenation>(
                        std::make_unique<regexp::Concatenation>(
                            std::make_unique<regexp::Symbol>('1'),
                            std::make_unique<regexp::Iteration>(
                                std::make_unique<regexp::Symbol>('0'))),
                        std::make_unique<regexp::Symbol>('1'))),
                std::make_unique<regexp::Symbol>('0'))));
    assert(wordsMatch(re3, {Word{'0', '1'}}) == std::set<size_t>{});
    assert(wordsMatch(re3, {Word{'0', '1', '1'}}) == std::set<size_t>{0});
    assert(wordsMatch(re3, {Word{'0', '1', '1', '0'}}) == std::set<size_t>{0});
    assert(wordsMatch(re3, {Word{'0', '1', '1', '0', '1', '1', '1', '0', '0', '0'}}) == std::set<size_t>{});
    assert(wordsMatch(re3, {Word{'0', '1', '1', '0', '1', '1', '1', '0', '0', '1'}}) == std::set<size_t>{0});
    assert(wordsMatch(re3, {Word{'0', '1', '1', '0', '1', '1', '1', '0', '0', '1', '0'}}) == std::set<size_t>{0});
    assert((wordsMatch(re3, {Word{'0', '1'}, Word{'0', '1', '1'}, Word{'0', '1', '1', '0'}, Word{'0', '1', '1', '0', '1', '1', '1', '0', '0', '0'}, Word{'0', '1', '1', '0', '1', '1', '1', '0', '0', '1'}, Word{'0', '1', '1', '0', '1', '1', '1', '0', '0', '1', '0'}}) == std::set<size_t>{1, 2, 4, 5}));
}
#endif
