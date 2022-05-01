#include <algorithm>
#include <array>
#include <cassert>
#include <ctime>
#include <functional>
#include <iostream>
#include <iterator>
#include <limits>
#include <numeric>
#include <queue>
#include <random>
#include <sstream>
#include <unordered_map>
#include <vector>
#include <chrono>
using namespace std::chrono;
using namespace std;

/*Hex game with artificial intelligence using Monte Carlo simulation.
Author:
 Romain Garnier <rom1{dot}garnier{at}yahoo{dot}fr>.
Licensing provisions:
 Apache 2.0 license.*/
 // Compile with
 // g++ -Wall -Wextra -Wpedantic -Wconversion HexAI.cpp -o HexAI
 // Execute with
 // ./HexAI dimension HumanVsHuman
 /*
    Human can play against human if second argument > 0.
    Machine chooses positions in the hex table and computes best move from
    a chosen number of Monte Carlo simulations (minimum 100, default 1000).
    Hex table is showed on terminal with played
    positions. Positions are numbered as a grid.
    X should take left<->right path to win.
    O should take up<->down path to win.
    The human might want to play in first or
    take machine position.
    Machine might want to take human position if the latest plays first.
    3 classes:
    Class Graph.
    Class Hex child class of Graph.
    Functor class gen_shift used to generate integers.
    Player should hit row number enter button,
    then column enter.
 */
/*Graph class is used for building the structure of the game by controlling the vertex and the edge.It can use various data structures like 
arrays, queues,... to update the vertex.  */
class Graph {
public:
    Graph(const size_t size = 7) : num_vertex(size) {
        adjacent_matrix.resize(num_vertex);
        weight_matrix.resize(num_vertex);
        neighbors.resize(num_vertex);
        vertices.resize(num_vertex);

        for (size_t i = 0; i < num_vertex; ++i) {
            adjacent_matrix[i].assign(num_vertex, false);
            weight_matrix[i].assign(num_vertex, 0.0);
            // Void string
            vertices[i] = blank;
        }//time complexity=O(n)
    } // Constructor overload with file name

    ~Graph() {}

    // Forbid copy constructor since we do not want to use it here
    Graph(const Graph&) = delete;


    inline size_t V() const { return num_vertex; }
    inline size_t E() {
        n_edges = 0;
        for (size_t x = 0; x < neighbors.size(); ++x) {
            n_edges += neighbors[x].size();
        }//time complexity=O(n)
        // x-y edge =y-x edge
        n_edges /= 2;
        return n_edges;
    }
    inline bool adjacent(const size_t& x, const size_t& y) {
        return adjacent_matrix[x][y];
    }

    inline std::string get_node_value(const size_t& x) { return vertices[x]; }

    inline void set_node_value(const size_t& x, const std::string& a) {
        vertices[x] = a;
    }

    inline void set_edge_value(const size_t& x, const size_t& y, const float& v) {
        if (adjacent_matrix[x][y]) { // First need to be created
            weight_matrix[x][y] = weight_matrix[y][x] = v;
        }
    }

    inline void add_edge(const size_t& x, const size_t& y) {
        if (!adjacent_matrix[x][y]) { // Add only if no edge already created
            adjacent_matrix[x][y] = true;
            neighbors[x].push_back(y);
            if (y != x) {
                adjacent_matrix[y][x] = true;
                neighbors[y].push_back(x);
            }
            set_edge_value(x, y, 0.0); // Set weight to 0.0
        }
    }

    inline void print_neighbors(const size_t& x) {
        std::cout << "List of neighboors of " << x << "\n";
        for (auto n : neighbors[x]) {
            std::cout << " " << n << ",";
        }
        std::cout << "\n";
    }//time complexity=O(n)

    inline void delete_edge(const size_t& x, const size_t& y) {
        if (adjacent_matrix[x][y]) { // Check it exists
            adjacent_matrix[x][y] = adjacent_matrix[y][x] = false;
            // The removed element is pushed to the end
            std::remove(neighbors[x].begin(), neighbors[x].end(), y);
            neighbors[x].pop_back();
            if (y != x) {
                std::remove(neighbors[y].begin(), neighbors[y].end(), x);
                // Resize for the removed element at the end
                neighbors[y].pop_back();
            }
        }
    }

    inline float get_edge_value(const size_t& x, const size_t& y) {
        return weight_matrix[x][y];
    }

    inline void PrintWeight() {

        for (size_t i = 0; i < num_vertex; i++) {
            for (size_t j = 0; j < num_vertex; j++) {

                std::cout << ", " << weight_matrix[i][j];
            }
        }//time complexity=O(n^2)
        std::cout << "\n";
    }

protected:
    // vertices map internal node indexes to node values
    std::vector<std::string> vertices;
    std::vector<std::vector<bool>> adjacent_matrix;
    std::vector<std::vector<float>> weight_matrix;
    std::vector<std::vector<size_t>> neighbors;
    size_t n_edges;
    size_t num_vertex;
    float m_density;
    float min_edge_length;
    float max_edge_length;
    const std::string blank = " . ";
};
//======================================================================================================
// Hex child class of Graph
// See https://en.wikipedia.org/wiki/Hex_(board_game)
// Pair (distance from source , node idx)
/*Hex class uses graph class to build the game depending on the inputs from the user or the machine.*/
typedef std::pair<float, size_t> ds_nidx;
class Hex : public Graph {
public:
    Hex(const size_t size = 7, const bool HumanVsHuman = false)
        : Graph(size* size), m_HvsH(HumanVsHuman) {
        num_cols = size;
        Left_indexes.resize(num_cols);
        // gen_shift generator function incrementing by first argument
        // Starting at second argument.
        gen_shift Left(num_cols, 0);
        std::generate(Left_indexes.begin(), Left_indexes.end(), Left);
        Right_indexes.resize(num_cols);
        gen_shift Right(num_cols, num_cols - 1);
        std::generate(Right_indexes.begin(), Right_indexes.end(), Right);

        Up_indexes.resize(num_cols);
        gen_shift Up(1, 0);
        std::generate(Up_indexes.begin(), Up_indexes.end(), Up);
        Down_indexes.resize(num_cols);
        gen_shift Down(1, num_cols * (num_cols - 1));
        std::generate(Down_indexes.begin(), Down_indexes.end(), Down);

        game_table.resize(num_cols);
        for (size_t i = 0; i < num_cols; ++i) {
            game_table[i].assign(num_cols, blank);
        }//time complexity=O(n)
        game_it = 0;
        previous_it = 0;

        Opposites[blue] = std::vector<bool>();

        Opposites[red] = std::vector<bool>();

        // Opposite side check existing
        Opposites[blue].assign(num_vertex, false);

        Opposites[red].assign(num_vertex, false);

        for (auto it = Right_indexes.begin(); it != Right_indexes.end(); ++it) {
            Opposites[blue][*it] = true;
        }//time complexity=O(n)

        for (auto it = Down_indexes.begin(); it != Down_indexes.end(); ++it) {
            Opposites[red][*it] = true;
        }//time complexity=O(n)

        local_neighbors.reserve(6);

        hex_graph();
    }

    ~Hex() {}

    // Forbid copy constructor since we do not want to use it here
    Hex(const Hex&) = delete;
    //---------------------------------------------------------------
 /*It shows how the game is displayed in terminal window.*/   
 void display_game() {
        for (size_t i = 0; i < num_cols; ++i) {
            std::cout << std::string(2 * i, ' ');
            for (size_t j = 0; j < num_cols; ++j) {
                std::cout << game_table[i][j];
                if (j < num_cols - 1) {
                    std::cout << "-";
                }
            }
            std::cout << " " << i;
            if (i < num_cols - 1) {
                std::cout << "\n";
                std::cout << std::string(2 * i + 1, ' ');
                std::generate_n(std::ostream_iterator<std::string>(std::cout, ""),
                    num_cols - 1, []() { return " \\ /"; });
                std::cout << " \\\n";
            }
            else { // Last line
                std::cout << "\n";
                std::cout << std::string(2 * (num_cols - 2) + 1, ' ');
                for (size_t j = 0; j < num_cols; ++j) {
                    std::cout << "  " << j << " ";
                }
                std::cout << "\n";
            }
        }//time complexity=O(n^2)
    }/*Overall time complexity=O(n^2)*/
    //-------------------------------------------------------------------------
  /*Deciding the result of the game dpending on the various cases.*/  
 bool game_over(std::string request_player, size_t num_trial) {

        if (game_it == 0 && !m_HvsH) {
            if (request_player == "x" || request_player == "X") {
                first_player = 1;
            }
            else {
                first_player = 0;
            }
        }

        if (play(num_trial)) {
            const std::string* current_player;
            std::vector<size_t>* BorderMin;
            // Iteration just played
            if (previous_it % 2) {
                current_player = &red;
                BorderMin = &Up_indexes;
                // BorderMax = &Down_indexes;
            }
            else {
                current_player = &blue;
                BorderMin = &Left_indexes;
                // BorderMax = &Right_indexes;
            }

            if (UnionFind(*BorderMin, *current_player, vertices)) {
                std::cout << "Game over, player " << *current_player << " wins!\n";
                return true;
            }

            if (game_it >= num_vertex) {
                std::cout << "Game over, draw game\n";
                return true;
            }

            return false;

        }
        else { // If play
            return false;
        }
    }

    //-----------------------------------------------------
    bool play(size_t num_trial) {
        const std::string* current_player;
        const std::string* current_path;
        std::string player_input;
        if (game_it == 0) {
            
            auto start = high_resolution_clock::now();  //measuring execution time of graph process
             
            display_game();

            auto stop = high_resolution_clock::now();
            auto duration = duration_cast<microseconds>(stop - start);
            std::cout << "execution time of graph process is: "<<duration.count() << " microseconds\n" ;
        }
        if (game_it % 2) {
            current_player = &red;
            current_path = &UpDown;
        }
        else {
            current_player = &blue;
            current_path = &LeftRight;
        }
        size_t col, row;

        std::cout << "Iteration number " << game_it << "\n";
        std::cout << "Player " << *current_player << ", path " << *current_path;
        std::cout << " please enter (row,column)"
            << "\n";
        // First player may not be machine if = 1
        if (m_HvsH || (game_it + first_player) % 2) {
            std::cin >> player_input;
            if (!(std::stringstream(player_input) >> row)) {
                std::cout << "Wrong input type, please enter \n";
                std::cout << "only numbers (row enter, column enter).\n";
                return false;
            }
            std::cin >> player_input;
            if (!(std::stringstream(player_input) >> col)) {
                std::cout << "Wrong input type, please enter number\n";
                return false;
            }

            if (row >= num_cols || col >= num_cols) {

                std::cout << "Illegal position," << *current_player
                    << "please play again"
                    << "\n";
                return false;
            }
            if (game_it == 0) {
                // Middle
                inv_map[0] = (num_cols) / 2;
                inv_map[1] = (num_cols) / 2;

                if (row == inv_map[0] && col == inv_map[1]) {
                    first_player++;
                    std::cout << "The machine has taken your position!\n";
                }
            }

        }
        else {
            std::cout << "Simulation running, please wait...\n";
            
            auto start = high_resolution_clock::now(); //measuring execution time of montecarlo alogorithm
            
            size_t vertex_num = MonteCarlo(*current_player, num_trial);
            
            auto stop = high_resolution_clock::now();
            auto duration = duration_cast<microseconds>(stop - start);
            std::cout << "execution time of montecarlo is: "<<duration.count() << " microseconds\n" ;
            
            
            inv_map = InvMapV(vertex_num);

            row = inv_map[0];
            col = inv_map[1];

            if (game_it == 0) {

                std::cout << "The machine has played "
                    << "(" << row << "," << col << ")"
                    << ".\n";
                std::cout << "Would you like to take his position ? y(yes), n(no) \n";

                std::string Input = "";
                std::cin >> Input;
                if (Input == "y" || Input == "Y") {
                    first_player++;
                    std::cout << "The human has taken your position\n";
                }
            }
        }

        if (game_table[row][col] == blank) {
            game_table[row][col] = *current_player;
            auto u = MapV(row, col);
            assert(u < num_vertex);
            vertices[u] = *current_player;
            std::cout << "Player " << *current_player << " has played "
                << "(" << row << "," << col << ")"
                << "\n";
            display_game();
            previous_it = game_it;
            game_it++;
            return true;
        }
        else {
            std::cout << "Illegal position," << *current_player << "please play again"
                << "\n";
            return false;
        }
    }
    //-------------------------------------------------------------------------

    void print_hex_graph() {
        display_game();
        for (size_t row = 0; row < num_cols; ++row) {
            for (size_t col = 0; col < num_cols; ++col) {
                auto u = MapV(row, col);
                std::cout << "Neighboors of " << row << "," << col << "\n";
                print_neighbors(u);
            }
        }
    }
    //-----------------------------------------------------------------------------
private:
    std::vector<std::vector<std::string>> game_table;
    // Boarder indexes (Left,Right,Up,Down)
    std::vector<size_t> Left_indexes;  // Left side indexes
    std::vector<size_t> Right_indexes; // Rigth side
    std::vector<size_t> Up_indexes;    // Up side
    std::vector<size_t> Down_indexes;  // Down side
    // Check if one node already browsed
    std::vector<bool> checked;
    // Mapping (row,col) with vertex number (row major)
    inline size_t MapV(const size_t& row, const size_t& col) {
        return row * num_cols + col;
    }
    std::array<size_t, 2> inv_map;
    inline std::array<size_t, 2> InvMapV(const size_t& v) {
        inv_map[0] = v / num_cols;
        inv_map[1] = v - inv_map[0] * num_cols;
        return inv_map;
    }
    const std::string blue = " X ";
    const std::string red = " O ";
    size_t game_it;
    size_t previous_it;
    // Increment if order first player switched
    size_t first_player = 0;
    //---------------------------------------------------------------------------------------
      // Class function object (functors):
    class gen_shift {
    public:
        gen_shift(size_t stride, size_t init) : m_stride(stride), m_init(init) {
            init = 0;
        }
        size_t operator()() {
            size_t init_tmp = m_init;
            m_init += m_stride;
            return init_tmp;
        }

    private:
        size_t m_stride, m_init;
    };
    //---------------------------------------------------------------------------------------
    std::vector<std::string> tmp_vertices;

    std::vector<size_t> mapping;
    std::vector<size_t> Identity;

    // PQ consist on a queue i.e
    // element is retrieved at front()
    // http://www.cplusplus.com/reference/queue/queue/pop/
    std::queue<size_t> PQ;

    std::vector<long int> win_prob;

    std::unordered_map<std::string, std::vector<bool>> Opposites;

    std::unordered_map<std::string, std::array<size_t, 2>> local_neighbors;
    bool m_HvsH;
    size_t num_cols;
    const float max_weight = 10.0;
    const std::string Up = "Up";
    const std::string Down = "Down";
    const std::string Left = "Left";
    const std::string Right = "Right";
    const std::string RightUp = "RightUp";
    const std::string DownLeft = "DownLeft";

    const std::string UpDown = "up-down";
    const std::string LeftRight = "left-right";
    // Array of dim (6,2) to generate neighboors of (rows,col) entries.
    // Using strings for the 6 neighboors makes it more clear
    // which (+,-) operation we are performing with a grid representation
    inline std::unordered_map<std::string, std::array<size_t, 2>>
        hex_neighbors(const size_t& row, const size_t& col) {
        //(row,col-1)
        local_neighbors[Left][0] = row;
        local_neighbors[Left][1] = std::max(static_cast<int>(col) - 1, 0);
        //(row,col+1)
        local_neighbors[Right][0] = row;
        local_neighbors[Right][1] = std::min(col + 1, num_cols - 1);
        //(row-1,col)
        local_neighbors[Up][0] = std::max(static_cast<int>(row) - 1, 0);
        local_neighbors[Up][1] = col;
        //(row+1,col)
        local_neighbors[Down][0] = std::min(row + 1, num_cols - 1);
        local_neighbors[Down][1] = col;

        //(row-1,col+1)
        local_neighbors[RightUp][0] = std::max(static_cast<int>(row) - 1, 0);
        local_neighbors[RightUp][1] = std::min(col + 1, num_cols - 1);
        //(row+1,col-1)
        local_neighbors[DownLeft][0] = std::min(row + 1, num_cols - 1);
        local_neighbors[DownLeft][1] = std::max(static_cast<int>(col) - 1, 0);

        return local_neighbors;
    }
    //---------------------------------------------------------------------------------------
    void hex_graph() {
        for (size_t row = 0; row < num_cols; ++row) {
            for (size_t col = 0; col < num_cols; ++col) {

                local_neighbors = hex_neighbors(row, col);

                auto u = MapV(row, col);

                for (auto row_col : local_neighbors) {
                    assert(row_col.second[0] < num_cols && row_col.second[0] < num_cols &&
                        "Problem i,j");
                    auto v = MapV(row_col.second[0], row_col.second[1]);
                    if (u != v) {
                        assert(u < num_vertex&& v < num_vertex && "Problem mapping");
                        add_edge(u, v);
                        set_edge_value(u, v, max_weight);
                        // All edges set to max_weight
                        // Set to zero when one connection created
                    }
                }//time complexity is O(n)
            }//time complexity is O(n)
        }//time complexity is O(n)
        
    }//worst case scenario is O(n^3)
    //---------------------------------------------------------------------------------------
    void clear_queue(std::queue<size_t>& q) {
        if (!q.empty()) {
            std::queue<size_t> empty;
            q = move(empty);
        }
    }//time complexity is O(1)
    //---------------------------------------------------------------------------------------
      /* union–find data structure is used for Finding shortest paths from src to all other vertices. */
    bool UnionFind(const std::vector<size_t>& BorderMin,
        const std::string& current_player,
        const std::vector<std::string>& vertice_name) {

        clear_queue(PQ);
        // Initialize checked edges to false : no neighbor checked yet
        checked.assign(num_vertex, false);
        // Start from all potential sources
        for (auto pt_src = BorderMin.begin(); pt_src != BorderMin.end(); ++pt_src) {
            if (vertice_name[*pt_src] == current_player) {

                PQ.push(*pt_src);

                while (!PQ.empty()) {
                    size_t u = PQ.front();
                    PQ.pop();
                    if (checked[u]) {
                        continue;
                    }
                    checked[u] = true;
                    for (auto v : neighbors[u]) {
                        if (vertice_name[v] == current_player) {
                            if (Opposites[current_player][v]) {
                                return true;
                            }
                            PQ.push(v);
                        }
                    }//time complexity is O(n)
                }//time complexity is O(n)
            }
        }//time complexity is O(n)
        return false;
        //worst case scenario is O(n^3)
    }
//-----------------------------------------------------------------------------------------
    size_t MonteCarlo(const std::string current_player, size_t num_trial) {
        tmp_vertices.assign(num_vertex, blank);
        win_prob.assign(num_vertex, 0);
        mapping.assign(num_vertex, 0);

        Identity.assign(num_vertex, 0);
        // Id mapping
        gen_shift Id(1, 0); // 0,1,2,3...
        std::generate(Identity.begin(), Identity.end(), Id);

        size_t count_non_blank = 0;
        size_t count_blank = game_it;
        for (size_t map = 0; map < vertices.size(); ++map) {
            if (vertices[map] != blank) {
                tmp_vertices[map] = vertices[map];
                mapping[count_non_blank] = map;
                count_non_blank++;
            }
            else {
                mapping[count_blank] = map;
                count_blank++;
            }
        }//time complexity is O(n)
        assert(game_it == count_non_blank);

        size_t middle_shuffle = (vertices.size() + count_non_blank) / 2;

        std::random_device rd;
        std::mt19937 g(rd());
        for (size_t trial = 0; trial < num_trial; trial++) {
            std::shuffle(Identity.begin() + count_non_blank, Identity.end(), g);
            // Need to assign each remaining vertex, red lower number since start
            // in second.
            for (size_t map = count_non_blank; map < middle_shuffle; ++map) {
                tmp_vertices[mapping[Identity[map]]] = red;
            }//time complexity is O(n)
            
            for (size_t map = middle_shuffle; map < vertices.size(); ++map) {
                tmp_vertices[mapping[Identity[map]]] = blue;
            }//time complexity is O(n)

            if (UnionFind(Up_indexes, red, tmp_vertices)) {
                // Increment indexes corresponding to red win
                if (current_player == red) { // Red win
                    for (size_t map = count_non_blank; map < middle_shuffle; ++map) {
                        win_prob[mapping[Identity[map]]]++;
                    }//time complexity is O(n)
                }
                else { // Blue lost
                    for (auto map = middle_shuffle; map < vertices.size(); ++map) {
                        win_prob[mapping[Identity[map]]]--;
                    }//time complexity is O(n)
                }
            }
            else {
                if (current_player == blue) { // Blue win
                    for (auto map = middle_shuffle; map < vertices.size(); ++map) {
                        win_prob[mapping[Identity[map]]]++;
                    }//time complexity is O(n)

                }
                else { // Red lost
                    for (size_t map = count_non_blank; map < middle_shuffle; ++map) {
                        win_prob[mapping[Identity[map]]]--;
                    }//time complexity is O(n)
                }
            }
        }//time complexity is O(n)
        
        // All accumulated sum are minimaly equal to -num_trial
        long int max = -static_cast<long int>(num_trial);
        size_t v_sol = 0;
        // Select among unselected vertices
        for (size_t map = 0; map < vertices.size(); ++map) {
            if (vertices[map] == blank && win_prob[map] > max) {
                max = win_prob[map];
                v_sol = map;
            }
        }
        return v_sol;
        //worst case scenario is complexity of order (n^2)
    }
//-----------------------------------------------------------------------------------------    
};
//=================================================================================================================
int getOnlyNumber1()
{
    int num;
    while (!(cin >> num)) {
        // Reset the input:
        cin.clear();
        // Get rid of the bad input before return was pressed:
        while (cin.get() != '\n')
        {
            continue;
        }
        // Ask user to try again:
        cout << "Please enter a number :  ";
    }
   
        while (num > 25 || num < 4) {
            cout << "please, enter valid number\n";
            while (!(cin >> num)) {
                // Reset the input:
                cin.clear();
                // Get rid of the bad input before return was pressed:
                while (cin.get() != '\n')
                {
                    continue;
                }
                // Ask user to try again:
                cout << "Please enter a number :  ";
            }
        }
        return num;
          //time complexity of this following function is O(n^3) but it is better in test case, it limits user to use dimension of [4 to 25] so we will use this implementation in enhancement, next implementation of order O(1)

    /*
    std::string num1;
    std::cin >> num1;
    double num_dim = 9.0;
    if (!(std::stringstream(num1) >> num_dim)) {
            num_dim = 9.0;
            std::cout << "Not a number -> default value chosen (9)\n";
        }
        return num_dim;
        */
        //time complexity is O(1)

} 

bool getOnlyNumber2()
{
    std::string num1;
    std::cin >> num1;
    double num_dim = 1.0;
    if (!(std::stringstream(num1) >> num_dim)) {
            num_dim = 1.0;
        }
        return num_dim;
}

   

//===========================================================================================
int main(int argc, char* argv[]) {

    int num_rows = 0;
    std::cout << "welcome to HEX-game\n";
    std::cout << "please enter number of rows you prefer to play of range[4-25]\n";
    num_rows = getOnlyNumber1();

    int HumanVsHuman;
    std::cout << "for [human vs machine] enter 0\n";
    std::cout << "for [human vs human] enter any other Input\n";
    HumanVsHuman = getOnlyNumber2();
    double num_trial = 1000.0;

    std::cout
        << "note: Player should hit row number+enter button, then column+enter.\n\n";
    if (argc == 2) {
        num_rows = atoi(argv[1]);
    }
    else if (argc == 3) {
        num_rows = atoi(argv[1]);
        HumanVsHuman = atoi(argv[2]);
    }
    std::cout << "Hex dimension " << num_rows << "\n";
    if (HumanVsHuman) {
        std::cout << "Human Vs Human \n\n";
    }
    else {
        std::cout << "Human Vs machine \n\n";
    }

    std::cout << "First player is X \n";
    std::cout << "Second player is O \n\n";
    std::string Input = "";
    std::string num_MCS;
    if (!HumanVsHuman) {
        std::cout
            << "for X Please enter \'x\' or \'X\' , for O enter \'O\' or any other input "
            << "\n";
        std::cin >> Input;
        std::cout << "Please enter number of montecarlo simulations (min=100, "
            "default=1000)\n";

        std::cin >> num_MCS;

        if (!(std::stringstream(num_MCS) >> num_trial)) {
            num_trial = 1000.0;
            std::cout << "Not a number -> default value chosen (1000)\n";
        }

        num_trial = std::max(100.0, num_trial);
        std::cout << "User has chosen " << num_trial << " Monte Carlo simulation\n";
    }
    Hex ST(num_rows, HumanVsHuman);
    // ST.print_hex_graph();
    // Play while non game over
    while (!ST.game_over(Input, static_cast<size_t>(num_trial)))
        ;
}
