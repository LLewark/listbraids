/* For a fixed genus given as command-line parameter, this program makes a
 * list of positive braid words and DT-codes of the corresponding closures,
 * such that the list is guaranteed to contain all prime positive braid knots
 * of that genus. Starting from genus 3, it will contain lots of doubles, which
 * must be removed with another method or program (e.g. knotscape) if one
 * wishes to obtain a list without doubles.
 *
 * The algorithm is a rather simple depth-first search, and all printed
 * braid-words have the following properties:
 *  - It is the lexicographic minimum among all its cyclic conjugates.
 *  - It cannot be made lexicographically smaller by shuffling two
 *    commuting Artin-generators, or
 *  - by a braid-like Reidemeister-III-move.
 *  - It is prime, gives a knot, and is of the correct genus.
 *  - Every generator occurs at least twice.
 *
 * If you wish to understand the algorithm, or tweak the program, you might
 * consider setting the global "debug" variable to true.
 *
 * With the GNU-compiler, you can compile e.g. using
 *    g++ -std=c++11 -O3 -o lb lb.C
 *
 * It would certainly be possible to optimize the program further for speed,
 * but it might not be worth the effort, since it only takes a couple of
 * second to run for genera up to 6, and still finishes in reasonable time
 * for genus 7 and 8.
 */
#include<vector>
#include<iostream>
#include<algorithm>

const bool debug = false;

int max(const std::vector<int> &b) {
    int result = 1;
    for (std::vector<int>::const_iterator i = b.begin(); i != b.end(); ++i)
        if (*i > result)
            result = *i;
    return result;
}

// needed only for DT-codes
class intpair {
    public:
        int o, e;
        bool s;
        bool operator<(const intpair &other) const {
            return o < other.o;
        }
};

// Prints the DT-code of a positive braid to std::cout.
// The braid is given as a vector v of integers, where i >= 1 corresponds to
// the sigma_i Artin generator
bool printDT(const std::vector<int> &v, int counter) {
    const int maxGen = max(v) - 1;
    std::vector<int> dt;
    std::vector<intpair> n;
    n.resize(v.size());
    int passed = 0;
    int c = 0;
    int crossingCounter = 1;
    do {
        for (std::vector<int>::const_iterator i = v.begin(); i != v.end(); ++i)
            if ((*i == c) || (*i == (c + 1))) {
                if (crossingCounter % 2)
                    n.at(i - v.begin()).o = crossingCounter;
                else
                    n.at(i - v.begin()).e = crossingCounter;
                n.at(i - v.begin()).s =
                    (!(crossingCounter % 2)) == (!(*i == c + 1));
                ++crossingCounter;
                if (*i == c + 1)
                    ++c;
                else
                    --c;
            }
        ++passed;
    } while (c != 0);
    if (passed != maxGen + 2)
        return false;
    std::sort(n.begin(), n.end());
    dt.resize(v.size());

    for (std::vector<intpair>::const_iterator i = n.begin(); i != n.end(); ++i)
        dt.at(i - n.begin()) = i->e * (i->s ? 1 : -1);
    std::cout << ": " << dt.size() << " " << counter;
    for (int j = 0; j < dt.size(); ++j)
        std::cout << " " << dt.at(j);
    std::cout << "\n";

    return true;
}

void printBraid(const std::vector<int> &b, std::ostream& s = std::cout,
        bool newline = true) {
    for (std::vector<int>::const_iterator i = b.begin(); i != b.end(); ++i)
        s << (char)(*i + 96);
    if (newline)
        s << "\n";
}

int sum(const std::vector<int> &b) {
    int result = 0;
    for (std::vector<int>::const_iterator i = b.begin(); i != b.end(); ++i)
        result += *i;
    return result;
}

/* The last letter is too high if there are more strands then maxB1 + 1,
 * or if the braid ends with sigma_i sigma_j, with j > i + 1.
 */
bool lastLetterTooHigh(const std::vector<int> &b, int maxB1) {
    if (b.size() < 2)
        return false;
    return (b.back() > 1 + *std::max_element(b.begin(), b.end() - 1));
}

int numberOfComponents(const std::vector<int> &b) {
    if (b.empty())
        return 0;
    std::vector<int> compNumber(max(b) + 1, 0);
    std::vector<int>::iterator i = compNumber.begin();
    int compCounter = 0;
    while (i != compNumber.end()) {
        compCounter += 1;
        while (*i == 0) {
            *i = compCounter;
            int currentPos = i - compNumber.begin() + 1;
            for (std::vector<int>::const_iterator j = b.begin();
                    j != b.end(); ++j) {
                if (*j == currentPos)
                    currentPos += 1;
                else if (*j == currentPos - 1)
                    currentPos -= 1;
            }
            i = compNumber.begin() + (currentPos - 1);
        }
        for (; (i != compNumber.end()) && (*i != 0); ++i);
    }
    return compCounter;
}

int b1(const std::vector<int> &b) {
    return 1 + b.size() - (max(b) + 1);
}

int missingCrossingsForPrimality(const std::vector<int> &b) {
    const int columns = max(b);
    std::vector<int> missingCrossings(columns, 0);
    for (int i = 1; i < columns; ++i) {
        int last = -1;
        int twistRegions = 0;
        for (std::vector<int>::const_iterator j = b.begin();
                j != b.end(); ++j) {
            if (((*j == i) || (*j == (i + 1))) && (*j != last)) {
                last = *j;
                ++twistRegions;
            }
        }
        if (debug && (twistRegions < 2))
            throw;
        if ((twistRegions == 2) && (missingCrossings.at(i - 1) == 0))
            missingCrossings.at(i - 1) = 1;
        if ((twistRegions < 4) && (missingCrossings.at(i) == 0))
            missingCrossings.at(i) = 1;
    }
    return sum(missingCrossings);
}

// Returs true if the braid is the lexicographic minimimum among all its
// cyclic conjugates.
bool lexicoGood(const std::vector<int> &b) {
    for (std::vector<int>::const_iterator i = b.begin() + 1; i != b.end(); ++i)
        if (std::lexicographical_compare(i, b.end(), b.begin(),
                    b.begin() + (b.end() - i)))
            return false;
    return true;
}

bool reidemeister(const std::vector<int> &b) {
    std::vector<int>::const_reverse_iterator i = b.rbegin();
    int s = *i;
    i += 1;
    while ((i != b.rend()) && ((*i < s - 1) || (*i > s + 1)))
        i += 1;
    if ((i == b.rend()) || (*i == s) || (*i == s + 1))
        return true;
    i += 1;
    while ((i != b.rend()) && ((*i < s - 1) || (*i > s + 1)))
        i += 1;
    if ((i == b.rend()) || (*i == s - 1) || (*i == s + 1))
        return true;
    return false;
}

/* Checks if the braid can be completed to an admissible braid word
 * of B1 = maxB1 by adding further letters.
 */
int completable(const std::vector<int> &b, int maxB1) {
    return (numberOfComponents(b) - (maxB1 - b1(b)) <= 1) +
           2 * (missingCrossingsForPrimality(b) <= (maxB1 - b1(b))) +
           4 * lexicoGood(b) + 
           8 * reidemeister(b);
}

void appendLetter(std::vector<int> &b) {
    b.push_back((b.back() == 1) ? 1 : (b.back() - 1));
}

void listBraids(int maxB1) {
    int counter = 0;
    std::vector<int> braid = { 1, 1 };
    // Depth-first search
    while (braid.size() > 1) {
        if (debug) {
            std::cerr << "Working on \"";
            printBraid(braid, std::cerr, false);
            std::cerr << "\". ";
        }
        if (lastLetterTooHigh(braid, maxB1)) {
            if (debug)
                std::cerr << "Last letter too high, popping back.\n";
            braid.pop_back();
            braid.back() += 1;
            continue;
        }
        if (debug)
            std::cerr << "Last letter good. ";
        int c;
        if ((c = completable(braid, maxB1)) != 15) {
            if (debug)
                std::cerr << "Not completable (" << c << "), increasing.\n";
            braid.back() += 1;
            continue;
        }
        if (debug)
            std::cerr << "Is completable. ";
        if (b1(braid) < maxB1) {
            if (debug)
                std::cerr << "Too short, appending.\n";
            appendLetter(braid);
            continue;
        }
        if (debug)
            std::cerr << "Is good!\n";
        counter += 1;
        printBraid(braid, std::cout, false);
        printDT(braid, counter);
        braid.back() += 1;
    }
}

int main(int argc, char** argv) {
    if (argc == 2) {
        const int g = atoi(argv[1]);
        std::cerr << "Working on genus " << g << ".\n";
        listBraids(2 * g);
    }  else
        std::cerr << "One positive integer as parameter required.\n";
    return 0;
}
