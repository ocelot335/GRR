#include <iostream>
#include <vector>
#include <functional>
#include <fstream>
#include <chrono>
#include <set>
#include "sstream"
#include "deque"
#include "list"
#include <deque>
#include <stdexcept>
#include <iostream>
#include <vector>
#include <bitset>
#include "sstream"
#include <queue>
#include <map>
#include <random>

//first = weights matrix, second = set of blockages
#define graph_t std::pair<std::vector<std::vector<int>>, std::set<std::pair<int, int>>>

//first = list of edges(weight, toVertex), second-first = map from apex's ids to graph's ids,
//second-second = id of t in apex tree
#define apexTree_t std::pair<std::vector<std::set<std::pair<int, int>>>, std::pair<std::vector<int>,int>>

graph_t *getGraph(int n, int e, int k) {
    auto gr = new graph_t{};
    e -= n - 1 + k;
    for (int i = 0; i < n; ++i) {
        gr->first.emplace_back();
        for (int j = 0; j < n; ++j) {
            gr->first[i].emplace_back(1e9);
        }
        gr->first[i][i] = 1e9;
    }

    std::list<int> nott{};
    for (int i = 0; i < n; ++i) {
        nott.push_back(i);
    }
    std::vector<int> there{};
    int cur = rand() % n;
    there.push_back(cur);
    nott.erase(std::find(nott.begin(), nott.end(), cur));
    for (int i = 0; i < n - 1; ++i) {
        auto tempnotthere = nott.begin();
        std::advance(tempnotthere, rand() % (nott.size()));

        auto tempthere = there.begin();
        std::advance(tempthere, rand() % (there.size()));

        int w = rand() % 5 + 1;

        gr->first[*tempnotthere][*tempthere] = w;
        gr->first[*tempthere][*tempnotthere] = w;

        there.push_back(*tempnotthere);

        nott.erase(tempnotthere);
    }

    for (int i = 0; i < k; ++i) {
        while (true) {
            int i_try = rand() % n;
            int j_try = rand() % (n - 1);
            /*if (i_try == 0 || j_try == 0) {
                continue;
            }*/
            if (j_try >= i_try) j_try++;
            if (gr->second.find(std::pair<int, int>{i_try, j_try}) == gr->second.end()
                && gr->first[i_try][j_try] == 1e9) {

                int w = 1;
                gr->first[i_try][j_try] = w;
                gr->first[j_try][i_try] = w;
                gr->second.insert(std::pair<int, int>{i_try, j_try});
                gr->second.insert(std::pair<int, int>{j_try, i_try});
                break;
            }
        }
    }

    for (int i = 0; i < e; ++i) {
        while (true) {
            int i_try = rand() % n;
            int j_try = rand() % (n - 1);
            if (j_try >= i_try) j_try++;

            int w = rand() % 5 + 1;

            if (gr->first[i_try][j_try] == 1e9) {
                gr->first[i_try][j_try] = w;
                gr->first[j_try][i_try] = w;
                break;
            }
        }
    }

    return gr;
}

//Дейкстра
std::pair<int, std::vector<int>> *findMin(graph_t *graph, int start, int end) {
    std::vector<std::vector<int>> &t = graph->first;
    int n = static_cast<int>(t.size());
    std::vector<int> p{};
    for (int i = 0; i < graph->first.size(); ++i) {
        p.emplace_back(-1);
    }
    std::set<std::pair<int, int>> weights{};
    std::vector<int> ans{};
    for (size_t i = 0; i < t.size(); ++i) { ans.push_back(2e9); }
    ans[start] = 0;
    weights.insert(std::pair<int, int>(0, start));
    std::pair<int, int> cur;
    while (!weights.empty()) {
        cur = *weights.begin();
        weights.erase(weights.begin());
        for (int i = 0; i < n; ++i) {
            if (t[cur.second][i] != 1e9) {
                if (t[cur.second][i] + cur.first < ans[i]) {
                    ans[i] = t[cur.second][i] + cur.first;
                    weights.insert({ans[i], i});
                    p[i] = cur.second;
                }
            }
        }
    }
    return new std::pair<int, std::vector<int>>{ans[end], p};
}

int optimal(graph_t *graph, int start, int end) {
    for (auto &edge : graph->second) {
        graph->first[edge.first][edge.second] = 1e9;
        graph->first[edge.second][edge.first] = 1e9;
    }
    return findMin(graph, start, end)->first;
}

int REPOSITION(graph_t *graph, int start, int end) {
    int cnt = 0;
    while (true) {
        auto check = findMin(graph, start, end);
        std::vector<int> path{};
        int temp = end;
        while (temp != start) {
            path.emplace_back(temp);
            temp = check->second[temp];
        }
        path.emplace_back(start);
        reverse(path.begin(), path.end());

        bool found_blocked = false;
        int temp_path = 0;
        for (int i = 0; i < path.size() - 1; ++i) {
            if (graph->second.find({path[i], path[i + 1]}) != graph->second.end()) {
                cnt += temp_path * 2;
                graph->first[path[i]][path[i + 1]] = 1e9;
                graph->first[path[i + 1]][path[i]] = 1e9;

                found_blocked = true;
                break;
            }

            temp_path += graph->first[path[i]][path[i + 1]];
        }
        if (found_blocked) continue;
        cnt += temp_path;
        break;
    }
    return cnt;
}

std::pair<std::vector<std::set<int>>, std::vector<std::vector<std::set<int>>>>
FindMultipleShortest(graph_t *graph, int start, int end, double alpha = 0.414) {
    auto minDist = findMin(graph, start, end);
    double distanceThreshold = (1 + alpha) * minDist->first;
    //Initialize
    std::set<int> Scur{end};
    std::set<int> Spast{};
    std::vector<std::vector<std::pair<int, int>>> edges{};
    int n = static_cast<int>(graph->first.size());
    int64_t sumOfDists = 0;
    int64_t numOfEdges = 0;
    for (int i = 0; i < n; ++i) {
        edges.emplace_back();
        for (int j = 0; j < n; ++j) {
            if (graph->first[i][j] != 1e9) {
                edges[i].emplace_back(graph->first[i][j], j);
                sumOfDists += graph->first[i][j];
                numOfEdges++;
            }
        }
    }

    std::vector<std::set<int>> Dv{};
    std::vector<std::vector<std::set<int>>> De{};

    for (int i = 0; i < n; ++i) {
        Dv.emplace_back();
        if (i == end) {
            Dv[i].insert(0);
        }
    }

    for (int i = 0; i < n; ++i) {
        De.emplace_back();
        for (int j = 0; j < n; ++j) {
            De[i].emplace_back();
            De[i][j].insert(1e9);
        }
    }

    //The algo
    for (int i = 0; i <= sumOfDists * numOfEdges; ++i) {
        Spast = Scur;
        std::set<int> temp{};
        Scur = temp;

        for (const int &vertex : Spast) {
            for (auto &edge : edges[vertex]) {
                if (edge.second == end) continue;
                Scur.insert(edge.second);
                for (const int &l : Dv[vertex]) {
                    auto &currentDe = De[edge.second][vertex];
                    if (edge.first + l > distanceThreshold) {
                        continue;
                    }
                    currentDe.insert(edge.first + l);
                    if (currentDe.size() > sumOfDists) {
                        currentDe.erase(--currentDe.end());
                    }
                }
            }
        }

        for (int j = 0; j < n; ++j) {
            if (j == end) continue;
            for (auto &edge : edges[j]) {
                for (const int &l : De[j][edge.second]) {
                    if (l > distanceThreshold) {
                        continue;
                    }
                    Dv[j].insert(l);
                    if (Dv[j].size() > sumOfDists) {
                        Dv[j].erase(--Dv[j].end());
                    }
                }
            }
        }
    }

    return std::pair<std::vector<std::set<int>>, std::vector<std::vector<std::set<int>>>>{Dv, De};
}

apexTree_t *implicitRepresentation(graph_t *graph, int start, int end, std::vector<std::set<int>> &Dv) {
    std::set<int> Scur{start};
    std::set<int> Spast{};
    int n = static_cast<int>(graph->first.size());
    std::vector<std::set<int>> Lcur(n);
    std::vector<std::set<int>> Lpast(n);

    Lcur[start] = Dv[start];
    //Lcur[start].insert(16);

    graph_t graphWithOnlyPaths{};
    auto *apexGraph = new apexTree_t{};
    for (int i = 0; i < n; ++i) {
        graphWithOnlyPaths.first.emplace_back();
        for (int j = 0; j < n; ++j) {
            graphWithOnlyPaths.first[i].emplace_back(1e9);
        }
    }

    std::vector<std::vector<std::pair<int, int>>> edges{};
    for (int i = 0; i < n; ++i) {
        edges.emplace_back();
        for (int j = 0; j < n; ++j) {
            if (graph->first[i][j] != 1e9) {
                edges[i].emplace_back(graph->first[i][j], j);
            }
        }
    }

    auto &apexCorresponding = apexGraph->second.first;
    std::map<std::pair<int, int>, int> corresponding{};
    for (const int &l : Lcur[start]) {
        corresponding[{start, l}] = apexCorresponding.size();
    }
    apexCorresponding.emplace_back(start);
    apexGraph->first.emplace_back();
    bool wasEndVertex = false;
    while (!Scur.empty()) {
        Spast = Scur;
        std::set<int> tempS{};
        Scur = tempS;

        Lpast = Lcur;
        std::vector<std::set<int>> tempL(n);
        Lcur = tempL;

        for (auto &u : Spast) {
            for (auto &edge : edges[u]) {
                int v = edge.second;
                bool thereIsEdge = false;
                for (const int &l : Lpast[u]) {
                    if (Dv[v].find(l - edge.first) != Dv[v].end()) {
                        if (Lcur[v].find(l - edge.first) == Lcur[v].end()) {
                            Lcur[v].insert(l - edge.first);
                            if ((v != end || !wasEndVertex) &&
                                corresponding.find({v, l - edge.first}) == corresponding.end()) {
                                corresponding[{v, l - edge.first}] = apexCorresponding.size();
                                if (v == end) {
                                    wasEndVertex = true;
                                    apexGraph->second.second = apexCorresponding.size();
                                }
                                apexCorresponding.emplace_back(v);
                                apexGraph->first.emplace_back();
                            }
                        }
                        apexGraph->first[corresponding[{u, l}]].insert({edge.first,
                                                                        corresponding[{v, l - edge.first}]});
                        thereIsEdge = true;
                    }
                }
                if (thereIsEdge) {
                    Scur.insert(v);
                    graphWithOnlyPaths.first[u][v] = edge.first;
                }
            }
        }
    }

    return apexGraph;
}

void setDistribution(std::vector<int> &corresponding, std::vector<std::vector<std::pair<int, int>>> &edgesTransposed,
                     std::vector<double> &probabilities,
                     std::vector<std::map<int, double>> &probabilitiesForEdges, int curId, int pastId,
                     std::set<std::pair<int, int>> &foundBlockages,
                     double p = 1) {
    if (pastId != -1) {
        probabilitiesForEdges[curId][pastId] += p;
    }
    if (curId == 0) return;
    int cntOfEdges = 0;
    std::vector<int> verticesToRecursion{};

    for (auto &edge : edgesTransposed[curId]) {
        if (foundBlockages.find({corresponding[curId], corresponding[edge.second]}) == foundBlockages.end()) {
            if (edge.second == 0) {
                probabilities[curId] += p;
            }
            cntOfEdges++;
            verticesToRecursion.emplace_back(edge.second);
        }
    }

    for (auto &vertex : verticesToRecursion) {
        setDistribution(corresponding, edgesTransposed, probabilities, probabilitiesForEdges, vertex, curId,
                        foundBlockages,
                        p / cntOfEdges);
    }
}

int getRandomId(std::map<int, double> &distribution) {
    std::random_device rd;
    std::mt19937 gen(rd());

    std::vector<double> probabilities;
    std::vector<int> ids;
    for (const auto &pair : distribution) {
        ids.push_back(pair.first);
        probabilities.push_back(pair.second);
    }
    std::discrete_distribution<> dist(probabilities.begin(), probabilities.end());

    int index = dist(gen);

    return ids[index];
}

//return <cost, status, number of found blockages>
std::pair<int, std::pair<bool, int>>
TraverseTreeProcedure(apexTree_t *apexTree, int start, int end, int k, graph_t *graph) {
    int endIdInApex = apexTree->second.second;
    int n = static_cast<int>(apexTree->first.size());

    std::vector<std::vector<std::pair<int, int>>> edgesTransposed(n);

    for (int i = 0; i < n; ++i) {
        for (auto &edge : apexTree->first[i]) {
            edgesTransposed[edge.second].emplace_back(edge.first, i);
        }
    }

    std::vector<double> probabilities(n);
    std::vector<std::map<int, double>> probabilitiesForEdges(n);
    std::set<std::pair<int, int>> foundBlockages{};
    setDistribution(apexTree->second.first, edgesTransposed, probabilities, probabilitiesForEdges, endIdInApex, -1,
                    foundBlockages, 1);


    std::vector<int> path{};


    int cost = 0;
    int numberOfBlockages = 0;

    bool maybeCanArrive = true;
    while (maybeCanArrive) {
        int cur = 0;
        path.clear();
        while (cur != endIdInApex) {
            path.emplace_back(cur);
            cur = getRandomId(probabilitiesForEdges[cur]);
        }
        path.emplace_back(endIdInApex);
        int tempCost = 0;
        int idToFindNewPath;
        for (int i = 0; i < path.size() - 1; ++i) {
            int idOfCurInGraph = apexTree->second.first[path[i]];
            int idOfNextInGraph = apexTree->second.first[path[i + 1]];
            if (graph->second.find({idOfCurInGraph, idOfNextInGraph}) !=
                graph->second.end()) {

                int beforeSize = foundBlockages.size();
                foundBlockages.insert({idOfCurInGraph, idOfNextInGraph});
                foundBlockages.insert({idOfNextInGraph, idOfCurInGraph});
                int afterSize = foundBlockages.size();
                if (beforeSize != afterSize) {
                    numberOfBlockages++;
                }
                graph->first[idOfCurInGraph][idOfNextInGraph] = 1e9;
                graph->first[idOfNextInGraph][idOfCurInGraph] = 1e9;
                cost += 2 * tempCost;
                idToFindNewPath = i + 1;
                break;
            } else {
                tempCost += graph->first[idOfCurInGraph][idOfNextInGraph];
            }
            if (path[i + 1] == endIdInApex) {
                cost += tempCost;
                return {cost, {true, numberOfBlockages}};
            }
        }
        std::vector<std::map<int, double>> probabilitiesFromEndUpdated(n);
        setDistribution(apexTree->second.first, edgesTransposed, probabilities, probabilitiesFromEndUpdated,
                        endIdInApex, -1,
                        foundBlockages, 1);
        for (int i = idToFindNewPath; i < path.size(); ++i) {
            if (probabilitiesFromEndUpdated[path[i]].empty() && path[i] != endIdInApex) {
                continue;
            }
            probabilitiesForEdges.clear();
            for (int j = 0; j < n; ++j) {
                probabilitiesForEdges.emplace_back();
            }
            setDistribution(apexTree->second.first, edgesTransposed, probabilities, probabilitiesForEdges,
                            path[i], -1,
                            foundBlockages, 1);
            if (!probabilitiesForEdges[0].empty()) {
                int tempcur = path[i];
                int temppast;
                while (tempcur != endIdInApex) {
                    temppast = tempcur;
                    tempcur = getRandomId(probabilitiesFromEndUpdated[tempcur]);
                    probabilitiesForEdges[temppast].insert({tempcur, 1});
                }
                break;
            }
            if (i == path.size() - 1) maybeCanArrive = false;
        }
    }

    return {cost, {false, numberOfBlockages}};
}

int GRR(graph_t *graph, int start, int end, int k, double alpha = 0.414) {
    int i = 0;
    int cnt = 0;

    do {

        if (rand() % (k - i + 1) == 0) {
            auto gr = FindMultipleShortest(graph, start, end, alpha);
            auto apex = implicitRepresentation(graph, start, end, gr.first);
            auto output = TraverseTreeProcedure(apex, start, end, 0, graph);
            cnt += output.first;
            if (output.second.first) {
                return cnt;
            }
            i += output.second.second;
        } else {
            auto check = findMin(graph, start, end);
            std::vector<int> path{};
            int temp = end;
            while (temp != start) {
                path.emplace_back(temp);
                temp = check->second[temp];
            }
            path.emplace_back(start);
            reverse(path.begin(), path.end());

            bool found_blocked = false;
            int temp_path = 0;
            for (int i = 0; i < path.size() - 1; ++i) {
                if (graph->second.find({path[i], path[i + 1]}) != graph->second.end()) {
                    cnt += temp_path * 2;
                    graph->first[path[i]][path[i + 1]] = 1e9;
                    graph->first[path[i + 1]][path[i]] = 1e9;
                    i++;
                    found_blocked = true;
                    break;
                }

                temp_path += graph->first[path[i]][path[i + 1]];
            }
            if (!found_blocked) return cnt + temp_path;
        }
        if (i == k) {
            return cnt + optimal(graph, start, end);
        }
    } while (true);
    return cnt;
}

int main() {
    srand(time(nullptr));
    int n, e, k;
    std::cin >> n >> e >> k;

    double sumGRR = 0;
    double sumREPOSITION = 0;
    double timeGRR = 0;
    double timeREPOSITION = 0;
    int trials = 100;
    for (int i = 0; i < trials; ++i) {
        graph_t *graph = getGraph(n, e, k);
        graph_t *graphcopy = new graph_t{};
        graphcopy->first = graph->first;
        graphcopy->second = graph->second;

        auto start = std::chrono::high_resolution_clock::now();
        double grr = (double) GRR(graph, 0, n - 1, k);
        auto end = std::chrono::high_resolution_clock::now();
        std::chrono::duration<double, std::milli> durationGRR = end - start;
        timeGRR += durationGRR.count();

        auto startR = std::chrono::high_resolution_clock::now();
        double reposition = (double) REPOSITION(graphcopy, 0, n - 1);
        auto endR = std::chrono::high_resolution_clock::now();
        std::chrono::duration<double, std::milli> durationREP = endR - startR;
        timeREPOSITION += durationREP.count();

        //int rep = REPOSITION(graph, 0, n - 1);
        int opt = optimal(graph, 0, n - 1);
        delete graph;
        sumREPOSITION += reposition / opt;
        sumGRR += grr / opt;
    }
    std::cout << "GRR: " << sumGRR / trials << "\n";
    std::cout << "REPOSITION: " << sumREPOSITION / trials << "\n\n";

    /*std::vector<std::vector<int>> trygr{};
    for (int i = 0; i < 8; ++i) {
        trygr.emplace_back();
        for (int j = 0; j < 8; ++j) {
            trygr[i].emplace_back(1e9);
        }
    }
    trygr[0][1] = 5;
    trygr[1][0] = 5;
    trygr[0][2] = 4;
    trygr[2][0] = 4;
    trygr[0][3] = 6;
    trygr[3][0] = 6;
    trygr[1][2] = 1;
    trygr[2][1] = 1;
    trygr[2][3] = 2;
    trygr[3][2] = 2;
    trygr[1][4] = 4;
    trygr[4][1] = 4;
    trygr[1][5] = 5;
    trygr[5][1] = 5;
    trygr[2][5] = 8;
    trygr[5][2] = 8;
    trygr[6][2] = 7;
    trygr[2][6] = 7;
    trygr[3][6] = 6;
    trygr[6][3] = 6;
    trygr[4][5] = 1;
    trygr[5][4] = 1;
    trygr[5][6] = 2;
    trygr[6][5] = 2;
    trygr[4][7] = 6;
    trygr[7][4] = 6;
    trygr[5][7] = 4;
    trygr[7][5] = 4;
    trygr[6][7] = 3;
    trygr[7][6] = 3;
    graph->first = trygr;
    graph->second.clear();
    graph->second.insert({2, 6});
    graph->second.insert({6, 2});
    graph->second.insert({4, 5});
    graph->second.insert({5, 4});
    graph->second.insert({0, 2});
    graph->second.insert({2, 0});*/


    /*std::cout << opt << " ";
    std::cout << grr << " ";
    std::cout << grr / opt << "\n";*/
    std::cout << "GRR boundary: " << (1 + 1 / 1.414) * k + 1.414 << "\n";
    std::cout << "REPOSTION boundary: " << 2 * k + 1 << "\n\n";

    std::cout << "GRR mean time: " << timeGRR / trials << "\n";
    std::cout << "REPOSTION mean time: " << timeREPOSITION / trials << "\n";
    return 0;
}
