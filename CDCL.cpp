/////////////////////////////////////////////ASSIGNMENT 2////////////////////////////////////////////////////////////////////////////////////////////
//                                  #Implementation of CDCL Algorithm                                                                              //
//                                  Author :BEDANTA DAS                                                                                            //
//                                          CS17MTECH11009                                                                                         //
//                                                                                                                                                 //
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
#include <iostream>
#include<vector>
#include<map>
#include<typeinfo>
#include<sstream>
#include<malloc.h>
#include<algorithm>

const int conflict = 1;
const int unresolved =2;
const int satisfied = 3;
const int unit = 4;

using namespace std;


//--------------------------------------------------------VARIABLE INITIALIZATION---------------------------------------------------------------------------//
struct literal{
    int value;
    int decision_level;
    int antecedant;
    vector<int> present_in;
};

int num_clause,num_lit;

//Watch-list data structure
vector<vector<int> > w;
vector<pair<int,int> >watchlist;


vector<int> conflict_clauses;
vector<int> assigned_literals;
//-----------------------------------------------------------------------------------------------------------------------------------------------------------//



//return true if all literals are assigned
bool is_allassigned(struct literal *l){
    //cout<<"hello";
    for(int i=1;i<=num_lit;i++){
            if(l[i].value==-1){
                return false;
            }
    }
    return true;
}

//fix up the watch pointers accordingly after unit propagation
void watchlist_fixup(struct literal *l){
    for(int i=0;i<watchlist.size();i++){
        if(watchlist[i].first > 0){
            if(l[abs(watchlist[i].first)].value==0){
                int flag = 0;
                for(int j=0;j<w[i].size();j++){
                    if(l[abs(w[i][j])].value==-1 && watchlist[i].second != w[i][j]){
                            watchlist[i].first = w[i][j];
                            flag = 1;
                        }
                    }
                if(flag==0){
                    for(int j=0;j<w[i].size();j++){
                        if(l[abs(w[i][j])].value==1 && watchlist[i].second != w[i][j]){
                            watchlist[i].first = w[i][j];
                        }
                    }
                }

            }
        }

        else if(watchlist[i].first < 0){
                if(l[abs(watchlist[i].first)].value==1){
                int flag = 0;
                for(int j=0;j<w[i].size();j++){
                    if(l[abs(w[i][j])].value==-1 && watchlist[i].second != w[i][j]){
                            watchlist[i].first = w[i][j];
                            flag = 1;
                        }
                    }
                if(flag==0){
                    for(int j=0;j<w[i].size();j++){
                        if(l[abs(w[i][j])].value==0 && watchlist[i].second != w[i][j]){
                            watchlist[i].first = w[i][j];
                        }
                    }
                }

            }
        }
        if(watchlist[i].second> 0){

             if(l[abs(watchlist[i].second)].value==0){
                int flag = 0;
                for(int j=0;j<w[i].size();j++){
                    if(l[abs(w[i][j])].value==-1 && watchlist[i].first != w[i][j]){
                            watchlist[i].second = w[i][j];
                            flag = 1;
                        }
                    }
                if(flag==0){
                    for(int j=0;j<w[i].size();j++){
                        if(l[abs(w[i][j])].value==1 && watchlist[i].first != w[i][j]){
                            watchlist[i].second = w[i][j];
                        }
                    }
                }

             }

        }
        else if(watchlist[i].second < 0){
             if(l[abs(watchlist[i].second)].value==1){
                int flag = 0;
                for(int j=0;j<w[i].size();j++){
                    if(l[abs(w[i][j])].value==-1 && watchlist[i].first != w[i][j]){
                            watchlist[i].second = w[i][j];
                            flag = 1;
                        }
                    }
                if(flag==0){
                    for(int j=0;j<w[i].size();j++){
                        if(l[abs(w[i][j])].value==0 && watchlist[i].first != w[i][j]){
                            watchlist[i].second = w[i][j];
                        }
                    }
                }

             }
        }

    }
}

//decide clause status based on watched-literal
int clause_status(struct literal *l,int clause_no){
    //cout<<"---------"<<endl;
    if(watchlist[clause_no].first>0 && watchlist[clause_no].second>0){
        if(watchlist[clause_no].first == watchlist[clause_no].second){
                if(l[abs(watchlist[clause_no].first)].value==-1){
                    return unit;
                }
                else if(l[abs(watchlist[clause_no].first)].value==0){
                    return conflict;
                }
                else if(l[abs(watchlist[clause_no].first)].value==1){
                    return satisfied;
                }
        }
        else if(l[abs(watchlist[clause_no].first)].value||l[abs(watchlist[clause_no].second)].value){
            return satisfied;
        }
        else if(l[abs(watchlist[clause_no].first)].value==-1 && l[abs(watchlist[clause_no].second)].value==-1){
            return unresolved;
        }
        else if(l[abs(watchlist[clause_no].first)].value==0 && l[abs(watchlist[clause_no].second)].value==0){
            //cout<<watchlist[clause_no].first<<endl;
            //cout<<watchlist[clause_no].second<<endl;
            conflict_clauses.push_back(clause_no);
            return conflict;

        }
        else if(l[abs(watchlist[clause_no].first)].value==-1&& l[abs(watchlist[clause_no].second)].value==0){
            return unit;
        }
        else if(l[abs(watchlist[clause_no].first)].value==0&& l[abs(watchlist[clause_no].second)].value==-1){
            return unit;
        }
    }
    else if(watchlist[clause_no].first<0 && watchlist[clause_no].second<0){
        //cout<<l[abs(watchlist[clause_no].first)].value;
        if(watchlist[clause_no].first == watchlist[clause_no].second){
             if(l[abs(watchlist[clause_no].first)].value==-1){
                    return unit;
                }
                else if(l[abs(watchlist[clause_no].first)].value==1){
                    return conflict;
                }
                else if(l[abs(watchlist[clause_no].first)].value==0){
                    return satisfied;
                }
        }
        else if(l[abs(watchlist[clause_no].first)].value==0 || l[abs(watchlist[clause_no].second)].value==0){
            return satisfied;
        }
        else if(l[abs(watchlist[clause_no].first)].value==-1 && l[abs(watchlist[clause_no].second)].value==-1){
            return unresolved;
        }
        else if(l[abs(watchlist[clause_no].first)].value==1 && l[abs(watchlist[clause_no].second)].value==1){
            //cout<<watchlist[clause_no].first<<endl;
            //cout<<watchlist[clause_no].second<<endl;
            conflict_clauses.push_back(clause_no);
            return conflict;

        }
        else if(l[abs(watchlist[clause_no].first)].value==-1 && l[abs(watchlist[clause_no].second)].value==1){
            return unit;
        }
        else if(l[abs(watchlist[clause_no].first)].value==1 && l[abs(watchlist[clause_no].second)].value==-1){
            return unit;
        }
    }
    else if(watchlist[clause_no].first<0 && watchlist[clause_no].second>0){
        if(l[abs(watchlist[clause_no].first)].value==0||l[abs(watchlist[clause_no].second)].value==1){
            return satisfied;
        }
        else if(l[abs(watchlist[clause_no].first)].value==-1 && l[abs(watchlist[clause_no].second)].value==-1){
            return unresolved;
        }
        else if(l[abs(watchlist[clause_no].first)].value==1 && l[abs(watchlist[clause_no].second)].value==0){
            //cout<<watchlist[clause_no].first<<endl;
            //cout<<watchlist[clause_no].second<<endl;
            conflict_clauses.push_back(clause_no);
            return conflict;

        }
        else if(l[abs(watchlist[clause_no].first)].value==-1 && l[abs(watchlist[clause_no].second)].value==0){
            return unit;
        }
        else if(l[abs(watchlist[clause_no].first)].value==1 && l[abs(watchlist[clause_no].second)].value==-1){
            return unit;
        }
    }
    else if(watchlist[clause_no].first>0 && watchlist[clause_no].second<0){
        if(l[abs(watchlist[clause_no].first)].value==1||l[abs(watchlist[clause_no].second)].value==0){
            return satisfied;
        }
        else if(l[abs(watchlist[clause_no].first)].value==-1 && l[abs(watchlist[clause_no].second)].value==-1){
            return unresolved;
        }
        else if(l[abs(watchlist[clause_no].first)].value==0 && l[abs(watchlist[clause_no].second)].value==1){
            //cout<<watchlist[clause_no].first<<endl;
            //cout<<watchlist[clause_no].second<<endl;
            conflict_clauses.push_back(clause_no);
            return conflict;

        }
        else if(l[abs(watchlist[clause_no].first)].value==-1&& l[abs(watchlist[clause_no].second)].value==1){
            return unit;
        }
        else if(l[abs(watchlist[clause_no].first)].value==0 && l[abs(watchlist[clause_no].second)].value==-1){
            return unit;
        }
    }

}

//set unit clause
void set_unit_clause(struct literal *l,int clause_no,int dl){
    if(l[abs(watchlist[clause_no].first)].value==-1 && watchlist[clause_no].first<0){
        l[abs(watchlist[clause_no].first)].value=0;
        l[abs(watchlist[clause_no].first)].decision_level=dl;
        l[abs(watchlist[clause_no].first)].antecedant=clause_no;
        assigned_literals.push_back(abs(watchlist[clause_no].first));
    }
    else if(l[abs(watchlist[clause_no].first)].value==-1 && watchlist[clause_no].first>0){
        l[abs(watchlist[clause_no].first)].value=1;
        l[abs(watchlist[clause_no].first)].decision_level=dl;
        l[abs(watchlist[clause_no].first)].antecedant=clause_no;
        assigned_literals.push_back(abs(watchlist[clause_no].first));
    }
    else if(l[abs(watchlist[clause_no].second)].value==-1 && watchlist[clause_no].second>0){
        l[abs(watchlist[clause_no].second)].value=1;
        l[abs(watchlist[clause_no].second)].decision_level=dl;
        l[abs(watchlist[clause_no].second)].antecedant=clause_no;
        assigned_literals.push_back(abs(watchlist[clause_no].second));
    }
    else if(l[abs(watchlist[clause_no].second)].value==-1 && watchlist[clause_no].second<0){
        l[abs(watchlist[clause_no].second)].value=0;
        l[abs(watchlist[clause_no].second)].decision_level=dl;
        l[abs(watchlist[clause_no].second)].antecedant=clause_no;
        assigned_literals.push_back(abs(watchlist[clause_no].second));
    }

    //after setting unit clause fix the watches
    watchlist_fixup(l);

}

//return conflict or set the unit literal
bool unit_propagation(struct literal *l,int dl){

    for(int i=0;i<w.size();i++){
           if(clause_status(l,i) == conflict){
                    return false;
            }

    }
    for(int i=0;i<w.size();i++){
           if(clause_status(l,i)==unit){
                set_unit_clause(l,i,dl);
                /*cout<<endl;
                for(int i=0;i<=watchlist.size();i++){

                cout<<watchlist[i].first<<" "<<watchlist[i].second<<endl;;
                }*/
                return unit_propagation(l,i);
            }
    }

    return true;
}

// backtrack to level back_ : set all variables default value for decision level > back_
void Backtrack(int back_,struct literal *l){
    for(int i=1;i<num_lit+1;i++){
        if(l[i].decision_level > back_ && l[i].value!=-1 ){
            l[i].value =-1;
            l[i].decision_level = -1;
            l[i].antecedant = -1;
        }
    }
}

//resolve two clauses  a and b and return the new clause (called in resolve conflict() method)
vector<int> resolve(vector<int> a, int antecedant){
    //cout<<"--------------"<<antecedant<<endl;
    /*for(vector<int>:: iterator it = a.begin();it!=a.end();it++){
        cout<<*it<<" ";
    }*/
    //cout<<endl;
    if(antecedant == -1){
        return a;
    }
    vector<int> b = w[antecedant];
    vector<int> resolved_clause;
    for(vector<int>::iterator it = a.begin();it!=a.end();it++){
        if(find(b.begin(),b.end(),*it)!= b.end()){
            resolved_clause.push_back(*it);
        }
        else if(find(b.begin(),b.end(),(*it))== b.end() && find(b.begin(),b.end(),-1*(*it))== b.end()){
            resolved_clause.push_back(*it);
        }
    }
    if(resolved_clause.size() == 0){
        return a;
    }
    return resolved_clause;

}

//checks if unit implication or not
int implication(vector<int> a,struct literal* l){
    int temp=0;
    for(vector<int>:: iterator it = a.begin();it!=a.end();it++){
        if(l[abs(*it)].antecedant != -1){
            temp++;
        }
    }
    return temp;
}


//find level to backtrack
int find_level(vector<int> a,struct literal *l,int dl,int uip){
    if(uip == 0){
        return(dl-1);
    }
    int temp = -1;
    for(vector<int>::iterator it=a.begin();it!=a.end();it++){
        if(temp > l[abs(*it)].decision_level && l[abs(*it)].decision_level != -1){
            temp = l[abs(*it)].decision_level;
        }
    }
    if(temp == -1){
        return(dl-1);
    }
    else{
        return temp;
    }
}

//compare if two vectors are same
bool is_equal(vector<int> a , vector<int> b){
    if(a.size()>0 && b.size()>0){
            sort(a.begin(),a.end());
            sort(b.begin(),b.end());
            return (a==b);
    }
    return true;
}
//resolve conflicting clause caused by deciding literal and unit propagation
int resolve_conflict(struct literal *l,int dl){

    int conflict_at =  conflict_clauses.back();
    conflict_clauses.pop_back();

    int unit_implication;
    int uip;

    vector<vector<int>> compare_clause;
    compare_clause.push_back(w[conflict_at]);

    for(vector<int>::iterator it = compare_clause.back().begin();it!=compare_clause.back().end();it++){
            //cout<<*it;
            if(!is_equal(resolve(compare_clause.back(),l[abs(*it)].antecedant),compare_clause.back())){
                compare_clause.push_back(resolve(compare_clause.back(),l[abs(*it)].antecedant));
            }
            uip = implication(compare_clause.back(),l);
            if(uip ==0){
                break;
            }
            /*else if(implication(compare_clause.back(),l)==compare_clause.back().size()){
                break;
            }*/
            //cout<<"jj";

    }
    /*for(vector<int>:: iterator it = compare_clause.back().begin();it!=compare_clause.back().end();it++){
        cout<<*it;
    }*/
    w.push_back(compare_clause.back());
    return (dl-1);//find_level(compare_clause.back(),l,dl,uip);

}

//decide and set variable
void set_variable(struct literal *l,int dl){
    for(int i=1;i<=num_lit;i++){
        if(l[i].value ==-1 ){
            l[i].value = 1;
            l[i].decision_level = dl;
            assigned_literals.push_back(i);
            watchlist_fixup(l);
            return;

        }
    }
}


bool CDCL(struct literal *l){
    if(unit_propagation(l,0)==false){
        return false;
    }
    int dl = 0;

    while(!is_allassigned(l)){
            set_variable(l,dl);
            //cout<<l[1].value;
            dl++;
            if(unit_propagation(l,dl)==false){
                //cout<<conflict_clauses[0];
                //cout<<"hello";
                int back_ = resolve_conflict(l,dl);
                //cout<<back_;
                if(back_ == 0){
                    return false;
                }
                else{
                    Backtrack(back_,l);
                    dl = back_;
                }
            }

    }

    return true;

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
    iss >> p >> cnf >> num_lit >> num_clause;

    int no_of_clauses = num_clause;

    struct literal l[num_lit];

    for(int i=0;i<=num_lit;i++){
        l[i].value = -1;
        l[i].decision_level = -1;
        l[i].antecedant = -1;
    }

    //input all the clauses
    while(no_of_clauses>0){
        getline(cin,line);
        istringstream iss(line);
        int literal;
        vector<int> cl;
        pair<int,int> p;
        while(iss >> literal){
            if(literal!=0){
                //l[literal].present_in.push_back(num_clause-no_of_clauses);
                cl.push_back(literal);
            }
        }
        w.push_back(cl);
        if(cl.size()==1){
            p.first = cl[0];
            p.second = cl[0];
        }
        else{
            p.first = cl[0];
            p.second = cl[1];
        }

        watchlist.push_back(p);
        no_of_clauses--;
    }

    if(CDCL(l)){
        cout<<"SAT"<<endl;
        for(int i=1;i<=num_lit;i++){
        if(l[i].value ==1){
            cout<<i<<" ";
        }
        else{
            cout<<-i<<" ";
        };
    }
    cout<<0<<endl;
    }
    else{
        cout<<"UNSAT"<<endl;
    }
    //cout<<clause_status(l,3);
    //cout<<l[abs(watchlist[0].first)].value<<" "<<watchlist[0].second;


    /*for(int i=0;i<=watchlist.size();i++){
        cout<<watchlist[i].first<<" "<<watchlist[i].second;
    }*/
    return 0;
}
