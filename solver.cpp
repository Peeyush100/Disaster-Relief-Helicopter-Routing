#ifndef SOLVER_H
#define SOLVER_H

#include <vector>
#include <cmath>
#include <algorithm>
#include <random>
#include <chrono>
#include <iostream>
#include <sstream>
#include <deque>
#include <numeric>
#include "structures.h"
#include <unordered_set>
#include <functional>

using namespace std;

static double MAX_TIME;
static chrono::steady_clock::time_point GLOBAL_START;

static mt19937 rng((unsigned)chrono::steady_clock::now().time_since_epoch().count());

inline int randInt(int a, int b) {
    static mt19937 rng{random_device{}()};
    return uniform_int_distribution<int>(a, b)(rng);
}

inline double randDouble(double a, double b) {
    static mt19937 rng{random_device{}()};
    return uniform_real_distribution<double>(a, b)(rng);
}

inline double Trip_weight(const Trip &t, const ProblemData &data) {
    return t.dry_food_pickup * data.packages[0].weight
         + t.perishable_food_pickup * data.packages[1].weight
         + t.other_supplies_pickup * data.packages[2].weight;
}
inline double trip_value(const Trip &t, const ProblemData &data) {
    return t.dry_food_pickup * data.packages[0].value
         + t.perishable_food_pickup * data.packages[1].value
         + t.other_supplies_pickup * data.packages[2].value;
}
inline double trip_Distance(const Trip &t, const Point &home, const ProblemData &data) {
    if (t.drops.empty()) return 0.0;
    double d = 0.0;
    Point cur = home;
    for (auto &drop : t.drops) {
        const Point &v = data.villages[drop.village_id - 1].coords;
        d += distance(cur, v);
        cur = v;
    }
    d += distance(cur, home);
    return d;
}
void Helicopter_pickups(Trip &t) {
    t.dry_food_pickup = 0;
    t.perishable_food_pickup = 0;
    t.other_supplies_pickup = 0;

    for (const auto &d : t.drops) {
        t.dry_food_pickup     += d.dry_food;
        t.perishable_food_pickup += d.perishable_food;
        t.other_supplies_pickup  += d.other_supplies;
    }
}
bool trip_possiblity(const Trip& trip, const Helicopter& heli, const Point&, const ProblemData& data) {
    return Trip_weight(trip, data) <= heli.weight_capacity + 1e-9 && trip_Distance(trip, data.cities[heli.home_city_id - 1], data) <= heli.distance_capacity + 1e-9;
}
bool plan_possiblity(const HelicopterPlan& plan, const Helicopter& heli, const ProblemData& data) {
    const Point& home = data.cities[heli.home_city_id - 1];
    double total_dist = 0;

    for (const auto& trip : plan.trips) {
        if (!trip_possiblity(trip, heli, home, data)) return false;
        total_dist += trip_Distance(trip, home, data);
    }
    return total_dist <= data.d_max + 1e-9;
}


bool soll_possiblity(const Solution& sol, const ProblemData& data) {
    if (sol.size() != data.helicopters.size()) return false;

    for (const auto& plan : sol) {
        if (plan.helicopter_id <= 0 || plan.helicopter_id > static_cast<int>(data.helicopters.size())) return false;
        if (!plan_possiblity(plan, data.helicopters[plan.helicopter_id - 1], data)) return false;
    }
    return true;
}


double Score_Calculate(const Solution& sol, const ProblemData& data) {
    if (!soll_possiblity(sol, data)) return -1e18;

    double value = 0, cost = 0;
    for (const auto& plan : sol) {
        const auto& heli = data.helicopters[plan.helicopter_id - 1];
        const auto& home = data.cities[heli.home_city_id - 1];

        for (const auto& trip : plan.trips) {
            if (trip.drops.empty()) continue;
            value += trip_value(trip, data);
            cost  += heli.fixed_cost + heli.alpha * trip_Distance(trip, home, data);
        }
    }
    return value - cost;
}


double villageUtility(const ProblemData& data, int, double food_need, double other_need, double dist) {
    double meals = food_need * max(data.packages[0].value, data.packages[1].value);
    double other = other_need * data.packages[2].value;
    return (meals + other) / (dist + 1e-6);
}



Solution makeGreedySol(const ProblemData& data) {
    const double Meal_per_person = 9.0, Other_per_Person = 1.0;

    Solution sol(data.helicopters.size());
    for (size_t i = 0; i < data.helicopters.size(); ++i)
        sol[i].helicopter_id = data.helicopters[i].id;

    vector<double> meals(data.villages.size()), other(data.villages.size());
    for (size_t i = 0; i < data.villages.size(); ++i) {
        meals[i] = data.villages[i].population * Meal_per_person;
        other[i] = data.villages[i].population * Other_per_Person;
    }

    for (size_t hi = 0; hi < data.helicopters.size(); ++hi) {
        const auto& heli = data.helicopters[hi];
        auto& plan = sol[hi];
        const auto& home = data.cities[heli.home_city_id - 1];
        double dist_used = 0;

        while (true) {
            Trip trip;
            Point pos = home;
            double w_left = heli.weight_capacity, d_left = heli.distance_capacity;
            bool dropped = false;

            for (int s = 0; s < (int)data.villages.size(); ++s) {
                int best = -1; double best_util = -1e100, best_dist = 0;

                for (int v = 0; v < (int)data.villages.size(); ++v) {
                    if (meals[v] < 1 && other[v] < 1) continue;
                    double to_v = distance(pos, data.villages[v].coords);
                    double back = distance(data.villages[v].coords, home);
                    if (to_v + back > d_left + 1e-9) continue;

                    double util = villageUtility(data, v, meals[v], other[v], to_v);
                    if (util > best_util) best = v, best_util = util, best_dist = to_v;
                }
                if (best == -1) break;

                int per = floor(min(meals[best], floor(w_left / data.packages[1].weight)));
                w_left -= per * data.packages[1].weight;
                int dry = floor(min(meals[best] - per, floor(w_left / data.packages[0].weight)));
                w_left -= dry * data.packages[0].weight;
                int oth = floor(min(other[best], floor(w_left / data.packages[2].weight)));
                w_left -= oth * data.packages[2].weight;

                if (per + dry + oth == 0) break;

                trip.drops.push_back({ data.villages[best].id, dry, per, oth });
                meals[best] -= per + dry;
                other[best] -= oth;
                d_left -= best_dist;
                pos = data.villages[best].coords;
                dropped = true;
            }
            if (!dropped) break;

            Helicopter_pickups(trip);
            double trip_dist = trip_Distance(trip, home, data);

            if (dist_used + trip_dist > data.d_max + 1e-9) {
                for (auto& drop : trip.drops) {
                    int v = drop.village_id - 1;
                    meals[v] += drop.perishable_food + drop.dry_food;
                    other[v] += drop.other_supplies;
                }
                break;
            }

            plan.trips.push_back(trip);
            dist_used += trip_dist;

            bool need_left = false;
            for (size_t i = 0; i < data.villages.size(); ++i)
                if (meals[i] > 1e-6 || other[i] > 1e-6) { need_left = true; break; }
            if (!need_left) break;
        }
    }

    for (auto& plan : sol)
        for (auto& trip : plan.trips)
            Helicopter_pickups(trip);

    return sol;
}



struct Neighbor {
    Solution sol;
    string move;
    bool valid;
    Neighbor(): valid(false) {}
};
vector<tuple<int,int,int>> getAllDropLocations(const Solution& sol) {
    vector<tuple<int,int,int>> locations;
    for (int h = 0; h < (int)sol.size(); ++h) {
        for (int t = 0; t < (int)sol[h].trips.size(); ++t) {
            for (int d = 0; d < (int)sol[h].trips[t].drops.size(); ++d) {
                locations.emplace_back(h, t, d);
            }
        }
    }
    return locations;
}

Neighbor swapDrops(const Solution& cur, const ProblemData&) {
    Neighbor out;
     auto locs = getAllDropLocations(cur);

    if (locs.size() < 2) return out;

    int i = randInt(0, (int)locs.size() - 1);
    int j; do j = randInt(0, (int)locs.size() - 1); while (j == i);

    int h1, t1, d1;
    tie(h1, t1, d1) = locs[i];
    int h2, t2, d2;
    tie(h2, t2, d2) = locs[j];

    out.sol = cur;
    swap(out.sol[h1].trips[t1].drops[d1], out.sol[h2].trips[t2].drops[d2]);
    Helicopter_pickups(out.sol[h1].trips[t1]);
    Helicopter_pickups(out.sol[h2].trips[t2]);

    out.move = "SWAP:" + to_string(h1) + "-" + to_string(t1) + "-" + to_string(d1) +
               "|" + to_string(h2) + "-" + to_string(t2) + "-" + to_string(d2);
    out.valid = true;
    return out;
}


Neighbor moveDrop(const Solution& cur, const ProblemData&) {
    Neighbor out;
     auto locs = getAllDropLocations(cur);

    if (locs.empty()) return out;

    int sh, st, sd;
    tie(sh, st, sd) = locs[randInt(0, (int)locs.size() - 1)];
    int dh = randInt(0, (int)cur.size() - 1);

    out.sol = cur;
    auto& src_trip = out.sol[sh].trips[st];
    Drop drop = src_trip.drops[sd];
    src_trip.drops.erase(src_trip.drops.begin() + sd);
    Helicopter_pickups(src_trip);
    if (src_trip.drops.empty())
        out.sol[sh].trips.erase(out.sol[sh].trips.begin() + st);

    auto& dest_plan = out.sol[dh];
    if (dest_plan.trips.empty() || randInt(0,3) == 0) {
        Trip trip; trip.drops.push_back(drop);
        Helicopter_pickups(trip);
        dest_plan.trips.push_back(trip);
        out.move = "MOVE:" + to_string(sh) + "->" + to_string(dh) + "-NEW";
    } else {
        int dt = randInt(0, (int)dest_plan.trips.size() - 1);
        dest_plan.trips[dt].drops.push_back(drop);
        Helicopter_pickups(dest_plan.trips[dt]);
        out.move = "MOVE:" + to_string(sh) + "->" + to_string(dh) + "-" + to_string(dt);
    }
    out.valid = true;
    return out;
}


Neighbor reorderTrip(const Solution& cur, const ProblemData&) {
    Neighbor neighbor;


    vector<pair<int, int>> candidateTrips;
    for (int heli = 0; heli < (int)cur.size(); ++heli) {
        for (int trip = 0; trip < (int)cur[heli].trips.size(); ++trip) {
            if (cur[heli].trips[trip].drops.size() >= 2) {
                candidateTrips.emplace_back(heli, trip);
            }
        }
    }

    if (candidateTrips.empty()) return neighbor;

    
    int idx = randInt(0, (int)candidateTrips.size() - 1);
    int helicopterIndex = candidateTrips[idx].first;
    int tripIndex = candidateTrips[idx].second;

    neighbor.sol = cur;
    auto& chosenTrip = neighbor.sol[helicopterIndex].trips[tripIndex];
    int totalDrops = chosenTrip.drops.size();


    int from = randInt(0, totalDrops - 2);
    int to   = randInt(from + 1, totalDrops - 1);
    reverse(chosenTrip.drops.begin() + from, chosenTrip.drops.begin() + to + 1);

    neighbor.move = "REORDER:heli=" + to_string(helicopterIndex) +
                    ",trip=" + to_string(tripIndex) +
                    ",from=" + to_string(from) +
                    ",to=" + to_string(to);

    neighbor.valid = true;
    return neighbor;
}


Neighbor tweakDrops(const Solution& cur, const ProblemData&) {
    Neighbor neighbor;

    auto dropSpots = getAllDropLocations(cur);

    if (dropSpots.empty()) return neighbor;

    int heliIdx, tripIdx, dropIdx;
    std::tie(heliIdx, tripIdx, dropIdx) = dropSpots[randInt(0, (int)dropSpots.size() - 1)];
    neighbor.sol = cur;

    auto& chosenDrop = neighbor.sol[heliIdx].trips[tripIdx].drops[dropIdx];
    chosenDrop.perishable_food = max(0, chosenDrop.perishable_food + randInt(-2, 3));
    chosenDrop.dry_food        = max(0, chosenDrop.dry_food        + randInt(-2, 2));
    chosenDrop.other_supplies  = max(0, chosenDrop.other_supplies  + randInt(-1, 1));

    Helicopter_pickups(neighbor.sol[heliIdx].trips[tripIdx]);
    neighbor.move = "TWEAK:H" + to_string(heliIdx) +
                    "-T" + to_string(tripIdx) +
                    "-D" + to_string(dropIdx);
    neighbor.valid = true;
    return neighbor;
}


Neighbor mergeTrips(const Solution& cur, const ProblemData& data) {
    Neighbor neighbor;

    vector<int> heliWithMultiTrips;
    for (int heli = 0; heli < (int)cur.size(); ++heli)
        if (cur[heli].trips.size() >= 2) heliWithMultiTrips.push_back(heli);

    if (heliWithMultiTrips.empty()) return neighbor;

    int heliIdx = heliWithMultiTrips[randInt(0, (int)heliWithMultiTrips.size() - 1)];
    int tripA = randInt(0, (int)cur[heliIdx].trips.size() - 1);
    int tripB = randInt(0, (int)cur[heliIdx].trips.size() - 1);
    while (tripB == tripA) tripB = randInt(0, (int)cur[heliIdx].trips.size() - 1);

    neighbor.sol = cur;

    Trip merged = neighbor.sol[heliIdx].trips[tripA];
    merged.drops.insert(merged.drops.end(),
                        neighbor.sol[heliIdx].trips[tripB].drops.begin(),
                        neighbor.sol[heliIdx].trips[tripB].drops.end());
    Helicopter_pickups(merged);


    const Helicopter& heli = data.helicopters[neighbor.sol[heliIdx].helicopter_id - 1];
    const Point& home = data.cities[heli.home_city_id - 1];
    if (!trip_possiblity(merged, heli, home, data)) return neighbor;

    if (tripA > tripB) swap(tripA, tripB);
    neighbor.sol[heliIdx].trips.erase(neighbor.sol[heliIdx].trips.begin() + tripB);
    neighbor.sol[heliIdx].trips.erase(neighbor.sol[heliIdx].trips.begin() + tripA);

    neighbor.sol[heliIdx].trips.push_back(merged);
    Helicopter_pickups(neighbor.sol[heliIdx].trips.back());

    neighbor.move = "MERGE:H" + to_string(heliIdx) +
                    "-T" + to_string(tripA) +
                    "-T" + to_string(tripB);
    neighbor.valid = true;
    return neighbor;
}



Solution tabuSearch(const Solution &start, const ProblemData &data) {
    Solution best = start;
    double bestScore = Score_Calculate(best, data);
    Solution cur = start;
    double curScore = bestScore;

    deque<string> tabuList; 
    unordered_set<string> tabuSet; 

    
    vector<function<Neighbor(const Solution&,const ProblemData&)>> ops = {
        moveDrop, swapDrops, reorderTrip, tweakDrops, mergeTrips
    };

    for (int iter=0; iter<8000; ++iter) {

        if (chrono::duration<double>(chrono::steady_clock::now() - GLOBAL_START).count() > MAX_TIME) break;
        Neighbor bestCand; double bestCandScore = -1e300; string bestMove="";

        for (int s=0; s<120; ++s) {
            int opIdx = randInt(0,(int)ops.size()-1);
            Neighbor cand = ops[opIdx](cur, data);
            if (!cand.valid) continue;

            if (!soll_possiblity(cand.sol, data)) continue;
            double sc = Score_Calculate(cand.sol, data);
            bool isTabu = (tabuSet.find(cand.move) != tabuSet.end());
            if (isTabu && sc <= bestScore + 1e-9) continue; 
            if (sc > bestCandScore) {
                bestCand = cand; bestCandScore = sc; bestMove = cand.move;
            }
        }
        if (!bestCand.valid) {
            continue;
        }

        cur = bestCand.sol;
        curScore = bestCandScore;


        tabuList.push_back(bestMove);
        tabuSet.insert(bestMove);
        if ((int)tabuList.size() > 400) {
            string rem = tabuList.front(); tabuList.pop_front();
            tabuSet.erase(rem);
        }

        
        if (curScore > bestScore + 1e-9) {
            best = cur; bestScore = curScore;
        }
        
    }

    if (Score_Calculate(best, data) + 1e-9 < Score_Calculate(start, data)) return start;
    return best;
}


Solution solve(const ProblemData& data) {
    GLOBAL_START = chrono::steady_clock::now();
    MAX_TIME = data.time_limit_minutes * 60.0 * 0.9;

    Solution greedy = makeGreedySol(data);
    if (!soll_possiblity(greedy, data)) {
        Solution emptySol;
        for (const auto& heli : data.helicopters)
            emptySol.push_back({heli.id});
        return emptySol;
    }

    double greedyScore = Score_Calculate(greedy, data);
    Solution bestSolution = greedy;
    double bestScore = greedyScore;

    for (int round = 0; round < 3; ++round) {
        Solution start = greedy;
        for (int p = 0; p < round; ++p) {
            Neighbor n = moveDrop(start, data);
            if (n.valid && soll_possiblity(n.sol, data))
                start = n.sol;
        }

        Solution improved = tabuSearch(start, data);
        double score = Score_Calculate(improved, data);

        if (score > bestScore + 1e-9) {
            bestSolution = improved;
            bestScore = score;
        }
    }

    if (bestScore <= 0) {
        Solution emptySol;
        for (const auto& heli : data.helicopters)
            emptySol.push_back({heli.id});
        return emptySol;
    }

    return bestSolution;
}

#endif 