
#include<set>
#include <iostream>
#include <cstdlib>
#include <fstream>
#include <string>
#include<cstring>
#include<vector>
#include<math.h>
#include <sstream>
#include<exception>
#include<unordered_map>
#include<assert.h>
using namespace std;

class Arg {
public:
    bool self_attacking = false;
    vector<int> attacks;
    unordered_map<string,int> attacksKey;
    int attacks_count;
    vector<int> attackedBy;
    unordered_map<string,int> attackedByKey;
    int attackedBy_count;
    string key;
    int id;
    vector<int> peerArgs;
    int peerArgs_count;
    Arg(int id, string key) {
        this->key = key;
        this->id = id;
    }

    Arg() {
    }
};
const char* inputFile; // contains the input argumentation framework in ASPARTIX/trivial format
unordered_map<string, int> arg_id; // a map of argument ids
vector<Arg> args; // set of arguments
const char IN = '1';
const char OUT = '0';
const char UNDEC = '3';
const char MUST_OUT = '2';
const char BLANK = '9';
const char MUST_IN = '7';
const char MUST_UNDEC = '8';
int args_count; // total number of arguments in the framework
vector< char* > labellings; // the preferred extensions to be build
const int activeArgs_max_size = 1000;
int activeArgs[activeArgs_max_size]; // implicit conflicts
long activeArgs_count = 0;

void readArgumentsASPARTIXFormat() { //reading an argumentation framework from an aspartix input file
    string inLine;
    ifstream infile;
    infile.open(inputFile);
    if(!infile){
    	cout<<"cannot find "<<inputFile<<endl;
    	exit(1);
	}
    infile>>inLine;
    int id = 1;
    while (!infile.eof() & inLine.find("arg") != string::npos) {
        string a = inLine.substr(4, inLine.find_last_of(")") - 4);
        arg_id[a] = id++;
        args.push_back(Arg(id, a));
        infile>>inLine;
    }
    while (!infile.eof()) {
        if (inLine.find("att") != string::npos) {
            string a = inLine.substr(4, inLine.find_last_of(",") - 4).c_str();
            string b = inLine.substr(inLine.find_last_of(",") + 1, inLine.find_last_of(")") - inLine.find_last_of(",") - 1).c_str();
            int a_id = arg_id[a]-1;
            int b_id = arg_id[b]-1;
            args[a_id].attacks.push_back(b_id);
            args[a_id].attacksKey[b]=b_id+1;
            args[b_id].attackedBy.push_back(a_id);
            args[b_id].attackedByKey[a]=a_id+1;
            if (a_id == b_id)
                args[a_id].self_attacking = true;
        }
        infile>>inLine;
    }
    infile.close();
}
void print() { //printing extensions to screen in the format: [[a0,a1,...],[a2,a7,...],...] 
    cout << "[";
    for (int j = 0; j < labellings.size(); j++) {
        if (j == 0)
            cout << "[";
        else
            cout << ",[";
        bool firstArg = true;
        for (int i = 0; i < args_count; i++) {
            if (labellings[j][i] == IN) {
                if (firstArg) {
                    cout << args[i].key;
                    firstArg = false;
                } else
                    cout << "," << args[i].key;
            }
        }
        cout << "]";
    }
    cout << "]";
    cout << endl;
}
int getActive(char *&labelling,int *&blank_attackers_count) { // select the most recent argument found conflicting in a dead-end
    int i = activeArgs_count - 1;
    int j = 0;
    int x;
    while (j < activeArgs_max_size && j < activeArgs_count) {
        int x = i % activeArgs_max_size;
        if (labelling[activeArgs[x]] == MUST_OUT) {
            if(blank_attackers_count[activeArgs[x]]>0){
                for (int k = 0; k < args[activeArgs[x]].attackedBy_count; k++) {
                    if (labelling[args[activeArgs[x]].attackedBy[k]] == BLANK)
                        return args[activeArgs[x]].attackedBy[k];
                }
            }
            else{
                activeArgs[activeArgs_count++ % activeArgs_max_size]=activeArgs[x];
                return -2;
            }
        }       
        j++;
        i--;
    }
    return -1;
}
int selectArg(char*&labelling,int *&blank_attackers_count,int *&undec_attackers_count) {//select an argument to be tried with the IN label
    int x = getActive(labelling,blank_attackers_count);
    if(x==-1){        
        for (int i = 0; i < args_count; i++) {
            if (labelling[i] == MUST_OUT){                
                if(blank_attackers_count[i]>0){
                    for(int j=0;j<args[i].attackedBy_count;j++){
                        if(labelling[args[i].attackedBy[j]]==BLANK)
                            return args[i].attackedBy[j];
                    }
                }
                else{
                    activeArgs[activeArgs_count++ % activeArgs_max_size]=i;
                    return -2;
                }
            }  
            else if(labelling[i] == BLANK && undec_attackers_count[i]>0)
                x=i;            
            else if(x==-1 && labelling[i]== BLANK)
                x=i;
        }      
    }
    return x;
}
bool isMaximal(vector<int> &extension) {
    for (int j = labellings.size() - 1; j >= 0; j--) {
        bool subset = true;
        for (int i = extension.size() - 1; i >= 0; i--) {            
            if (labellings[j][extension[i]] != IN) {
                subset = false;
                break;
            }
        }
        if (subset) {
            return false;
        }
    }
    return true;
}

bool analyze_undec(int x,vector<int> &mustUndec, vector<int> &mustIN_args, int *&undec_attackers_count, int *&blank_attackers_count, char * &labelling){
    for(int i=0;i<args[x].attacks.size();i++){
        int y=args[x].attacks[i];
        if(labelling[y]!=OUT && labelling[y]!=MUST_IN){
            blank_attackers_count[y]--;
            undec_attackers_count[y]++;        
            if(blank_attackers_count[y]==0 && labelling[y]==MUST_OUT){
                activeArgs[activeArgs_count++ % activeArgs_max_size]=y;
                return false;
            }
            //y is already defended with mutual attacks
            if(blank_attackers_count[y] == 0 && undec_attackers_count[y] <= args[y].peerArgs_count && labelling[y] == BLANK){
                int c=0;
                for(int s=0;s<args[y].peerArgs_count;s++){
                    if(labelling[args[y].peerArgs[s]]== UNDEC){
                        c++;
                    }
                }
                if(c==undec_attackers_count[y]){
                    mustIN_args.push_back(y);
                    labelling[y] = MUST_IN;
                }
            }
            if(blank_attackers_count[y]==0 && undec_attackers_count[y]==1){
                if(labelling[y]==UNDEC || labelling[y]==MUST_UNDEC){ 
                    //x is the only undec attacker
                    for(int j=0;j<args[x].attackedBy.size();j++){
                        int z=args[x].attackedBy[j];
                        if(labelling[z]==BLANK){
                            labelling[z]=MUST_UNDEC;
                            mustUndec.push_back(z);
                        }
                        else if(labelling[z]==MUST_IN)
                            return false;
                    }                    
                }
            } 
            if(blank_attackers_count[y]==0 && undec_attackers_count[y]>0){
                if(labelling[y]==BLANK || labelling[y]==UNDEC || labelling[y]==MUST_UNDEC){
                    for(int j=0;j<args[y].attacks.size();j++){
                        int z=args[y].attacks[j];
                        if(labelling[z]==BLANK){
                            labelling[z]=MUST_UNDEC;
                            mustUndec.push_back(z);
                        }
                        else if(labelling[z]==MUST_IN)
                            return false;
                    }
                }
            }
            if(blank_attackers_count[y]==1 && labelling[y]==MUST_OUT){
                for(int j=0;j<args[y].attackedBy.size();j++){
                    int z=args[y].attackedBy[j];
                    if(labelling[z]==BLANK){
                        labelling[z]=MUST_IN;
                        mustIN_args.push_back(z);
                        break;
                    }
                    else if(labelling[z]==MUST_UNDEC)
                        return false;
                }
            }
        }
    } 
    return true;
}
bool undec_transition(int x,vector<int> &mustUndec, vector<int> &mustIN_args, int *&undec_attackers_count, int *&blank_attackers_count, char * &labelling){
    labelling[x]=UNDEC;
    if(blank_attackers_count[x]==0 && undec_attackers_count[x]==0)
        return false;
    if(blank_attackers_count[x]==0 && undec_attackers_count[x]>0){
        for(int i=0;i<args[x].attacks.size();i++){
            int y=args[x].attacks[i];
            if(labelling[y]==BLANK){
                labelling[y]=MUST_UNDEC;
                mustUndec.push_back(y);
            }
            else if(labelling[y]==MUST_IN)
                return false;
        }
    }
    if(blank_attackers_count[x]==0 && undec_attackers_count[x]==1){
        int w;
        for(int i=0;i<args[x].attackedBy.size();i++){
            w=args[x].attackedBy[i];
            if(labelling[w]==UNDEC){
                break;
            }
        }
        for(int i=0;i<args[w].attackedBy.size();i++){
            int z=args[w].attackedBy[i];
            if(labelling[z]==BLANK){
                labelling[z]=MUST_UNDEC;
                mustUndec.push_back(z);
            }
            else if(labelling[z]==MUST_IN)
                return false;
        }
    }
    return analyze_undec(x,mustUndec, mustIN_args, undec_attackers_count, blank_attackers_count, labelling);
}
bool analyze_in(char xPreviousLabel,int x,vector<int> &mustUndec, vector<int> &mustIN_args, int *&undec_attackers_count, int *&blank_attackers_count, char * &labelling){
    for(int i=0;i<args[x].attacks.size();i++){
        int y=args[x].attacks[i];
        if(xPreviousLabel==UNDEC)
            undec_attackers_count[y]--;
        else
            blank_attackers_count[y]--;
        if(labelling[y]!= IN && labelling[y]!=OUT && labelling[y]!=MUST_IN){
            if(xPreviousLabel!=UNDEC || labelling[y]!=MUST_OUT){
                if(xPreviousLabel!=UNDEC){
                    if(labelling[y]==MUST_OUT && blank_attackers_count[y]==0){
                        activeArgs[activeArgs_count++ % activeArgs_max_size]=y;
                        return false;
                    }
                    if(labelling[y]==BLANK||labelling[y]==UNDEC||labelling[y]==MUST_UNDEC){
                        if(blank_attackers_count[y]==0 && undec_attackers_count[y]>0){
                            for(int j=0;j<args[y].attacks.size();j++){
                                int z=args[y].attacks[j];                              
                                if(labelling[z]==BLANK){                                
                                    labelling[z]=MUST_UNDEC;
                                    mustUndec.push_back(z);                                
                                }
                                else if(labelling[z]==MUST_IN)
                                    return false;                            
                            }
                        }
                    }
                    if(blank_attackers_count[y]==1 && labelling[y]==MUST_OUT){
                        for(int j=0;j<args[y].attackedBy.size();j++){
                            int z=args[y].attackedBy[j];                        
                            if(labelling[z]==BLANK){
                                labelling[z]=MUST_IN;
                                mustIN_args.push_back(z);
                                break;                            
                            }
                            else if(labelling[z]==MUST_UNDEC)
                                return false;                        
                        }
                    }   
                }                
                if(labelling[y]==UNDEC || labelling[y]==MUST_UNDEC)
                    if(undec_attackers_count[y]==0 && blank_attackers_count[y]==0)
                        return false;
                if(labelling[y]==BLANK && blank_attackers_count[y]==0){
                    if(undec_attackers_count[y]==0){
                        labelling[y]=MUST_IN;
                        mustIN_args.push_back(y);
                    }
                    else if(undec_attackers_count[y] <= args[y].peerArgs_count){
                        int c=0;
                        for(int s=0;s<args[y].peerArgs_count;s++){                            
                            if(labelling[args[y].peerArgs[s]]== UNDEC){
                                c++;
                            }                            
                        }
                        if(c==undec_attackers_count[y]){
                            mustIN_args.push_back(y);
                            labelling[y] = MUST_IN;
                        }
                    }
                }
                if(labelling[y]==UNDEC || labelling[y]==MUST_UNDEC){
                    if(undec_attackers_count[y]==1 && blank_attackers_count[y]==0){
                        int w;
                        for(int j=0;j<args[y].attackedBy.size();j++){
                            w=args[y].attackedBy[j];
                            if(labelling[w]==UNDEC){  
                                break;                                   
                            }
                        }                           
                        for(int j=0;j<args[w].attackedBy.size();j++){
                            int z=args[w].attackedBy[j];                            
                            if(labelling[z]==BLANK){                                
                                labelling[z]=MUST_UNDEC;
                                mustUndec.push_back(z);                                
                            }
                            else if(labelling[z]==MUST_IN)
                                return false;                            
                        }
                    }
                }                
            }
        }
    }
    return true;
}
bool in_transition(int s,vector<int> &mustUndec, vector<int> &mustIN_args, int *&undec_attackers_count, int *&blank_attackers_count, char *&labelling){
    labelling[s]=IN;
    for(int i=0;i<args[s].attacks.size();i++){
        int x=args[s].attacks[i];
        if(labelling[x]!=OUT){            
            if(labelling[x]==MUST_IN)
                return false;
            if(labelling[x]==UNDEC || labelling[x]==MUST_UNDEC || labelling[x]==BLANK){
                char xPreviousLabel=labelling[x];
                labelling[x]=OUT;
                if(analyze_in(xPreviousLabel,x,mustUndec,mustIN_args,undec_attackers_count,blank_attackers_count,labelling)==false)
                    return false;
            }
            else if(labelling[x]==MUST_OUT)
                labelling[x]=OUT;           
        }
    }
    for(int i=0;i<args[s].attackedBy.size();i++){        
        int x=args[s].attackedBy[i];
        if(labelling[x]!=OUT && labelling[x]!=MUST_OUT){
            if(labelling[x]==MUST_IN)
                    return false;
            if(blank_attackers_count[x]==0){
               activeArgs[activeArgs_count++ % activeArgs_max_size]=x;
               return false;
            }
            char xPreviousLabel=labelling[x];
            labelling[x]=MUST_OUT;
            if(blank_attackers_count[x]==1){
                for(int j=0;j<args[x].attackedBy.size();j++){
                    int z=args[x].attackedBy[j];
                    if(labelling[z]==BLANK){
                        labelling[z]=MUST_IN;
                        mustIN_args.push_back(z);
                        break;
                    }
                    else if(labelling[z]==MUST_UNDEC)
                        return false;
                }            
            }
            if(analyze_in(xPreviousLabel,x,mustUndec,mustIN_args,undec_attackers_count,blank_attackers_count,labelling)==false)
                return false;
        }
    }
    return true;
}
// new
bool analyzeIn(char xPreviousLabel,int x,vector<int> &mustUndec, vector<int> &mustIN_args, int *&undec_attackers_count, int *&blank_attackers_count, char * &labelling){
    for(auto y:args[x].attacks){
        blank_attackers_count[y]--;
        if(blank_attackers_count[y]==0){
            if(labelling[y]==MUST_OUT){
                activeArgs[activeArgs_count++ % activeArgs_max_size]=y;
                return false;
            }
            else if(labelling[y]==BLANK){
                labelling[y]=MUST_IN;
                mustIN_args.push_back(y);
            }
        }
        else if(blank_attackers_count[y]==1){
            //? 存疑，原代码没这么写
            if(labelling[y]==MUST_OUT || labelling[y]==OUT){
                for(auto z:args[y].attackedBy){
                    if(labelling[z]==BLANK){
                        labelling[z]=MUST_IN;
                        mustIN_args.push_back(z);
                        break;
                    }
                }
            }
        }
    }
}
// new
bool inTransition(int s,vector<int> &mustUndec, vector<int> &mustIN_args, int *&undec_attackers_count, int *&blank_attackers_count, char * &labelling){
    labelling[s]=IN;
    for(auto x:args[s].attacks){
        if(labelling[x]!=OUT){
            if(labelling[x]==MUST_IN)return false;
            if(labelling[x]==MUST_OUT)labelling[x]=OUT;
            else if(labelling[x]==BLANK){
                char xPreviousLabel=labelling[x];
                labelling[x]=OUT;
                if(analyze_in(xPreviousLabel,x,mustUndec,mustIN_args,undec_attackers_count,blank_attackers_count,labelling)==false)
                    return false;
            }
            else assert(0);
        }
    }
    for(auto x:args[s].attackedBy){
        if(labelling[x]==MUST_IN)return false;
        else if(labelling[x]==BLANK){
            if(blank_attackers_count[x]==0){
               activeArgs[activeArgs_count++ % activeArgs_max_size]=x;
                return false;
            }
            char xPreviousLabel=labelling[x];
            labelling[x]=MUST_OUT;
            if(blank_attackers_count[x]==1){
                for(auto z:args[x].attackedBy){
                    if(labelling[z]==BLANK){
                        labelling[z]=MUST_IN;
                        mustIN_args.push_back(z);
                        break;
                    }
                }
            }
            if(analyze_in(xPreviousLabel,x,mustUndec,mustIN_args,undec_attackers_count,blank_attackers_count,labelling)==false)
                return false;
        }
    }
    return true;
}
bool outTransition(int s,vector<int> &mustUndec, vector<int> &mustIN_args, int *&undec_attackers_count, int *&blank_attackers_count, char * &labelling){
    if(blank_attackers_count[s]==0)return false;
    else if (blank_attackers_count[s] == 1) {
        for (auto x : args[s].attackedBy) {
            if (labelling[x] == BLANK) {
                labelling[x] = MUST_IN;
                mustIN_args.push_back(x);
                break;
            }
        }
    }
    char xPreviousLabel=labelling[s];
    labelling[s]=MUST_OUT;
    analyzeIn(xPreviousLabel, s, mustUndec, mustIN_args, undec_attackers_count, blank_attackers_count, labelling);
    return true;
}
bool propagate(vector<int> &extension,vector<int> &mustUndec, vector<int> &mustIN_args, int *&undec_attackers_count, int *&blank_attackers_count, char * &labelling){
    while(mustIN_args.empty()==false){
        int i=mustIN_args[mustIN_args.size()-1];
        mustIN_args.pop_back();
        if(labelling[i]!=MUST_IN)
            return false;
        if(in_transition(i,mustUndec, mustIN_args, undec_attackers_count, blank_attackers_count, labelling)==false)
            return false;
        extension.push_back(i);
    }
    return true;
}
void preferred(vector<int> extension,vector<int> &mustUndec, vector<int> &mustIN_args, int *&undec_attackers_count, int *&blank_attackers_count, char * &labelling, int &n) {// recursive function for finding n extensions, all if n=-1 {    
    if(propagate(extension,mustUndec, mustIN_args, undec_attackers_count, blank_attackers_count, labelling)==false)
        return;
    int selectedArg = selectArg(labelling,blank_attackers_count,undec_attackers_count);
    if(selectedArg>=0){
        vector<int> mustIN_args1;
        vector<int> mustUndec1;
        char *labelling1 = new char[args_count];
        int *blank_attackers_count1 = new int[args_count];
        int *undec_attackers_count1 = new int[args_count];        
        for (int j = 0; j < args_count; j++) {
            labelling1[j] = labelling[j];
            blank_attackers_count1[j] = blank_attackers_count[j];
            undec_attackers_count1[j] = undec_attackers_count[j];
        }
        if(inTransition(selectedArg,mustUndec1, mustIN_args1, undec_attackers_count1, blank_attackers_count1, labelling1)==true){
            preferred(extension,mustUndec1, mustIN_args1, undec_attackers_count1, blank_attackers_count1, labelling1,n);
        }
        delete[] labelling1;
        delete[] blank_attackers_count1;
        delete[] undec_attackers_count1;     
        if(outTransition(selectedArg, mustUndec, mustIN_args, undec_attackers_count, blank_attackers_count, labelling)==true)
            preferred(extension,mustUndec, mustIN_args, undec_attackers_count, blank_attackers_count, labelling,n);
    }
    else if (selectedArg == -1) { // no must-out arg
        char* labelling1 = new char[args_count];
        for (int k = 0; k < args_count; k++)
            labelling1[k] = labelling[k];
        labellings.push_back(labelling1);
        n--;
        if (n == 0) {
            print();
            exit(0);
        }
    }    
}
void compare() {
    ifstream fin("g_11576075__7191__1_1_1__82730612.apx.EE-ST");
    if (!fin) {
        cout << "!" << endl;
        exit(0);
    }
    string s;
    set<string>a, b;
    fin >> s;
    s = s.substr(2, s.size() - 4);
    int pos,p=0;
    while ((pos = s.find(',',p)) != string::npos) {
        a.insert(s.substr(p, pos - p));
        p = pos+1;
    }
    a.insert(s.substr(p,100));

    for (int j = 0; j < labellings.size(); j++) {
        for (int i = 0; i < args_count; i++) {
            if (labellings[j][i] == IN) {
                b.insert(args[i].key);
            }
        }
    }
    for (auto i : a)cout << i << " ";
    cout<<endl;
    cout << (a == b ? "Yes" : "No") << endl;
}
/**
 * @date 2023/10/30
 */
int main(int argc, char* arguments[]) {
     int n = atoi(arguments[1]); // 0 means find all extentions, otherwise it finds n extensions
     inputFile = arguments[2];
    //int n = 0;
    readArgumentsASPARTIXFormat();
    args_count = args.size();    
    char *labelling = new char[args_count];
    int *undec_attackers_count = new int[args_count];
    int *blank_attackers_count = new int[args_count];//the number of blank/mustIN/mustUNDEC attackers
    vector<int> mustIn;
    vector<int> mustUndec;    
    //initialization
    for (int i = 0; i < args_count; i++) {        
        args[i].attacks_count = args[i].attacks.size();
        args[i].attackedBy_count = args[i].attackedBy.size();
        blank_attackers_count[i] = args[i].attackedBy_count;
        undec_attackers_count[i] = 0;
        if(args[i].self_attacking == false){
            //finding peer arguments
            for(int j=0;j<args[i].attacks_count;j++){
                string k=args[args[i].attacks[j]].key;
                if(args[i].attacksKey[k] == args[i].attackedByKey[k]){
                    args[i].peerArgs.push_back(args[i].attacks[j]);                    
                }
            }             
        }
        args[i].peerArgs_count=args[i].peerArgs.size();
    }     
    for (int i = 0; i < args_count; i++) {
        if (args[i].self_attacking) {
            labelling[i]=MUST_OUT;
            for (auto x : args[i].attacks) {
                blank_attackers_count[x]--;
            }
        } else {
            labelling[i] = BLANK;            
            //already defended arguments must IN
            if (blank_attackers_count[i] == 0 && undec_attackers_count[i] == 0) {
                mustIn.push_back(i);
                labelling[i] = MUST_IN;
            }            
        }        
    }      
    //end initialization     
    vector<int> extension;
    preferred(extension, mustUndec,mustIn,undec_attackers_count, blank_attackers_count, labelling, n);
    print();
    return 0;
}
