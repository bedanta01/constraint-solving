///////////////////////////////////////////////////////////////////////////////
//               IMPLEMENTATION OF DPLL ALGORITHM                            //
//          Author : CS17MTECH11009 : BEDANTA KUMAR DAS                      //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////


#include <iostream>
#include<map>
#include<vector>
#include<typeinfo>
#include<sstream>
#include<map>
#include<algorithm>

using namespace std;

int vars,no_of_clauses;

//final assignment to literals
map<int, bool> sol;


//function to sort clause vector w.r.t size
bool sort_clause(const vector<int> a,const vector<int> b){
        return (a.size()<b.size());
    }


bool dpll(vector< vector<int> > clauses,map<int,bool> assigned){

    vector< vector<int> > :: iterator i;
    vector<int>:: iterator j;

    // function remove all the true clauses : check assigned map if a literal is set
    auto remove_true_clause = [&](vector<int>i)->bool{
        vector<int>:: iterator it;
        bool is_true = false;
        for(it=i.begin();it!=i.end();it++){

            if(assigned.find(abs(*it))!=assigned.end()){
                if(*it<0){
                    is_true = (assigned[abs(*it)]+1)%2;
                }
                else if(*it>0){
                    is_true = assigned[abs(*it)];
                }
            }
        }
        return is_true;
    };

    // function to remove all the false literals from clauses: check assigned map if a literal is set
    auto remove_false_literal=[&](int num)->bool{
        return((assigned.find(abs(num))==assigned.end())?false:(num<0?assigned[abs(num)]:((assigned[abs(num)]+1)%2)));
    };


    //remove false literals
    for(i=clauses.begin();i<clauses.end();i++){
        auto iterator = remove_if(i->begin(),i->end(),remove_false_literal);
        i->erase(iterator,i->end());
    }

    //remove true clauses
    auto iterator = remove_if(clauses.begin(),clauses.end(),remove_true_clause);
    clauses.erase(iterator,clauses.end());

    if(clauses.size()==0){
        // assign solution to the global solution map
        sol = assigned;
        return true;
    }

    //check if a clause is empty : if yes return false
    for(vector< vector<int> > :: iterator i=clauses.begin();i!=clauses.end();i++){
            if(i->empty()){
               return false;
        }
    }

    vector<vector<int> > clause_copy;

    //unit propagation
    int temp = 0;
    for(i=clauses.begin();i!=clauses.end();i++){
        if(i->size()==1){
            clause_copy = clauses;
            j = i->begin();
            if(*j<0){
                sol[abs(*j)] = false;
                assigned[abs(*j)] = false;
            }
            else{
                int index = *j;
                sol[index] = true;
                assigned[index] = true;
            }
            //remove the unit clause
            clause_copy.erase(clause_copy.begin()+temp);
            return dpll(clause_copy,assigned);

        }
        temp++;


    }

    // sort the clause vectors w.r.t size and select the minimum clause to set TRUE/FALSE value
    sort(clauses.begin(),clauses.end(),sort_clause);
    clause_copy = clauses;
    for(i=clause_copy.begin();i<clause_copy.end();i++){
            for(j=i->begin();j!=i->end();j++){

                    assigned[abs(*j)] = false;
                    bool l = dpll(clause_copy,assigned);
                    if(l==true){
                        return true;
                    }

                    assigned[abs(*j)] = true;
                    bool m = dpll(clause_copy,assigned);
                    return (m);
            }

    }


return false;

}

int main()
{
    string line;
    string p,cnf;
    vector< vector<int> > clauses;
    map<int, bool> assigned;

    // ignore comments till 'p is encountered'
    while(getline(cin,line)){
        if(line[0]== 'p'){
            break;
        }
    };
    istringstream iss(line);
    iss >> p >> cnf >> vars >> no_of_clauses;

    //input all the clauses
    while(no_of_clauses>0){
        getline(cin,line);
        istringstream iss(line);
        int literal;
        vector<int> c;
        while(iss >> literal){
            if(literal!=0){
                c.push_back(literal);
            }

        }
        clauses.push_back(c);
        no_of_clauses--;
    }

    bool sat = dpll(clauses,assigned);
    if(sat){
        cout<<"SAT"<<endl;
        for(map<int ,bool>::iterator p=sol.begin();p!=sol.end();p++){
        //cout<<p->first<<" "<<p->second;
        if(p->second == 0){
            cout<<"-"<<p->first<<" ";
        }
        else{
            cout<<p->first<<" ";
        }
        }
        cout<<endl;
    }
    else{
        cout<<"UNSAT"<<endl;
    }

    return 0;
}
