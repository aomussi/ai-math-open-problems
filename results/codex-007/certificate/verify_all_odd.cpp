// Complete finite-state certificates for four infinite odd-length families
// in Kotzig Nim {3,5}, together with exact minimax for all n <= 33.
// No input data, external libraries, SAT solver, or network are required.
// Every counterexample accepted by the automaton is checked as an actual play.
#include <bits/stdc++.h>
using namespace std;
using u32=uint32_t;
using u64=uint64_t;

int baseline=41, boundary_width=16, lap_feature=0, prologue=16, epilogue=16;
int initial_step=0;
int policy_laps=1, end_phase=4, variable_count=1024;
string policy;
// Bit p of each row specifies whether to prefer +5 for occupancy pattern p.
// Pattern bits, from least significant, inspect offsets {-3,-5,+1,-1,+2,-2}.
// All other cases prefer +3; if preferred move is blocked use the other one.
const array<u64,40> PREFER5_1 = {
    0x0000008000000600ull, // mid v%8=0
    0x8000200000002000ull, // mid v%8=1
    0x000000a000000000ull, // mid v%8=2
    0x4080000000000002ull, // mid v%8=3
    0x0000000000000200ull, // mid v%8=4
    0x6080600000000006ull, // mid v%8=5
    0x0000008000000200ull, // mid v%8=6
    0xc080a00000002006ull, // mid v%8=7
    0x0000000000000000ull, // lo v=0
    0x6000200020002000ull, // lo v=1
    0x8000002000000000ull, // lo v=2
    0x0000000000000000ull, // lo v=3
    0x0000000004000440ull, // lo v=4
    0x8000800000000004ull, // lo v=5
    0x8000000000000600ull, // lo v=6
    0x0000000000000000ull, // lo v=7
    0x0000008000000000ull, // lo v=8
    0xc000200040000000ull, // lo v=9
    0x8000002000000200ull, // lo v=10
    0x2080000020000000ull, // lo v=11
    0x0000000006000460ull, // lo v=12
    0x6080e00000000006ull, // lo v=13
    0x8000008000080200ull, // lo v=14
    0xe080800020000006ull, // lo v=15
    0x0000000000000000ull, // hi n-v=1
    0x0000000000040000ull, // hi n-v=2
    0x0000000000000000ull, // hi n-v=3
    0x0000000000000004ull, // hi n-v=4
    0x0000000000000000ull, // hi n-v=5
    0xa080000020000000ull, // hi n-v=6
    0x000000c000000620ull, // hi n-v=7
    0xe080000020000000ull, // hi n-v=8
    0x0000008000000600ull, // hi n-v=9
    0x6080200000000006ull, // hi n-v=10
    0x000000c006000200ull, // hi n-v=11
    0x0000000000000006ull, // hi n-v=12
    0x0000000000000000ull, // hi n-v=13
    0x0000000020000006ull, // hi n-v=14
    0x8000000000000620ull, // hi n-v=15
    0xc000200000000000ull  // hi n-v=16
};
const array<u64,12> PREFER5_3 = {
    0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull,
    0, 0, 0, 0, 0, 0, 0, 0, 0
};
const array<u64,12> PREFER5_5 = {
    0, 0, 0, 0xffffffffffffffffull, 0xffffffffffffffffull,
    0xaaaaaaaaaaaaaaaaull, 0, 0, 0, 0, 0, 0
};
const array<u64,16> PREFER5_7 = {
    0x0000008000000000ull, 0x0080000000000000ull,
    0x0000002002000020ull, 0x0000000000000006ull,
    0x0000002006000600ull, 0x8000800000000006ull,
    0x0000000000000600ull, 0xe080000000000000ull,
    0x0000000000000000ull, 0x8000000000002000ull,
    0x0000004000000000ull, 0x0000000000000000ull,
    0x0000000000000000ull, 0x0000000000000000ull,
    0x0000000000000000ull, 0x0000000000000004ull
};

int lap(int c){return c?(c-1)/3:-100;}
int type(int c){return c?(c-1)%3:3;}
int code(int l,int t){return 1+3*l+t;}
array<int,5> decode(u32 h){array<int,5> c;for(int i=0;i<5;i++)c[i]=(h>>(5*i))&31;return c;}
u32 encode(array<int,5> c){u32 h=0;for(int i=0;i<5;i++)h|=u32(c[i])<<(5*i);return h;}
u32 shift(u32 h,int c){return (h>>5)|(u32(c)<<20);}
u32 add_lap(u32 h){auto c=decode(h);for(int &x:c)if(x)x+=3;return encode(c);}

bool admissible(u32 h){
    auto c=decode(h);int last[5];fill(last,last+5,-1);
    int pending=0,targets=0,terminal=-1;
    for(int i=0;i<5;i++){
        int l=lap(c[i]);if(l<0)continue;if(l>4)return false;
        if(last[l]>=0){int j=last[l];if(i-j!=3||type(c[j])!=0)return false;}
        last[l]=i;
    }
    for(int i=0;i<5;i++)if(c[i]){
        int t=type(c[i]),l=lap(c[i]);
        if(t==2){if(terminal>=0)return false;terminal=l;if(last[l]!=i)return false;continue;}
        int dest=i+(t==0?3:5);
        if(dest<5){if(lap(c[dest])!=l)return false;}
        else{int bit=1<<(dest-5);if(targets&bit)return false;targets|=bit;pending|=1<<l;}
    }
    if(pending&(pending+1))return false;
    if(terminal>=0&&terminal!=__builtin_popcount((unsigned)pending))return false;
    return true;
}

struct State{u32 h;int f;bool operator==(const State&s)const{return h==s.h&&f==s.f;}};
int key(int region,int pattern,int l){return (region*64+pattern)*policy_laps+(lap_feature?l:0);}
bool prefer_five(int region,int pattern,int l){return policy[key(region,pattern,l)]=='1';}

vector<State> step(State state,int phase,int region,int end_distance=-1,bool start=false){
    auto c=decode(state.h);
    auto incoming=[&](int a,int ta,int b,int tb){
        bool aa=type(c[a])==ta,bb=type(c[b])==tb;
        if(aa&&bb)return -200;
        if(aa)return lap(c[a]);
        if(bb)return lap(c[b]);
        return -100;
    };
    int l=incoming(2,0,0,1);if(l==-200)return {};
    if(start){if(l>=0)return {};l=0;}
    if(l<0){if(state.f&1)return {};return {{shift(state.h,0),state.f>>1}};}
    if(l>4)return {};
    int l1=incoming(3,0,1,1),l2=incoming(4,0,2,1);
    if(l1==-200||l2==-200)return {};
    if(end_distance==1){if(l1>=0)return {};l1=-1;}
    if(end_distance==2){if(l2>=0)return {};l2=-1;}
    int l3=type(c[3])==1?lap(c[3]):-100;
    if(end_distance==3){if(l3>=0)return {};l3=-1;}
    bool block3=l3!=-100&&l3<l;
    bool block5=end_distance==5||(l2!=-100&&l2<l);
    bool second=(phase+l)&1;
    int pattern=0;
    if(lap(c[2])>=0&&lap(c[2])<=l)pattern|=1;
    if(lap(c[0])>=0&&lap(c[0])<=l)pattern|=2;
    if(l1!=-100&&l1<l)pattern|=4;
    if(lap(c[4])>=0&&lap(c[4])<=l)pattern|=8;
    if(l2!=-100&&l2<l)pattern|=16;
    if(lap(c[3])>=0&&lap(c[3])<=l)pattern|=32;
    bool prefer=prefer_five(region,pattern,l);
    vector<State> result;
    for(int t=0;t<3;t++){
        if(start&&initial_step&&(t==2||(t==0?3:5)!=initial_step))continue;
        if((state.f&1)&&t!=0)continue;
        bool force=false;
        if(t==0){
            if(l3!=-100||end_distance==3)continue;
            if(second&&prefer){if(!block5)continue;force=end_distance!=5;}
        }else if(t==1){
            if(end_distance==5)continue;
            if(second&&!prefer&&!block3)continue;
        }else{
            if(!second||!block3||!block5)continue;
            force=end_distance!=5;
        }
        result.push_back({shift(state.h,code(l,t)),(state.f>>1)|(force?2:0)});
    }
    return result;
}

vector<u32> histories;
unordered_map<u32,int> history_id;
vector<array<int,2>> adjacency;
vector<vector<int>> accepting;
vector<pair<u32,int>> boundaries;
map<pair<u32,int>,int> boundary_id;

int state_id(State s,int phase){
    auto it=history_id.find(s.h);if(it==history_id.end())return -1;
    return (it->second*4+s.f)*8+phase;
}
pair<State,int> decode_state(int id){
    int phase=id%8;id/=8;int f=id%4;id/=4;
    return {{histories[id],f},phase};
}
vector<State> unique_states(vector<State> states){
    sort(states.begin(),states.end(),[](State x,State y){return tie(x.h,x.f)<tie(y.h,y.f);});
    states.erase(unique(states.begin(),states.end()),states.end());return states;
}
vector<int> unique_ids(vector<int> ids){sort(ids.begin(),ids.end());ids.erase(unique(ids.begin(),ids.end()),ids.end());return ids;}

void initialize(){
    for(u32 h4=0;h4<(1u<<20);h4++){
        array<int,5> c;for(int j=0;j<5;j++)c[j]=(h4>>(4*j))&15;
        u32 h=encode(c);if(admissible(h)){history_id[h]=histories.size();histories.push_back(h);}
    }
    for(u32 h:histories){auto c=decode(h);if(type(c[0])!=1&&type(c[2])!=0)
        for(int f=0;f<4;f++)boundaries.push_back({h,f});}
    for(int b=0;b<(int)boundaries.size();b++)boundary_id[boundaries[b]]=b;
    adjacency.resize(histories.size()*4*8);accepting.resize(adjacency.size());
}

void build_graph(){
    for(int id=0;id<(int)adjacency.size();id++){
        adjacency[id]={-1,-1};accepting[id].clear();
        auto [s,p]=decode_state(id);int k=0;
        for(State next:step(s,p,p))if(admissible(next.h)){
            if(k==2)throw runtime_error("unexpected outdegree");
            adjacency[id][k++]=state_id(next,(p+1)%8);
        }
        if(p!=end_phase)continue;
        vector<State> front={s};
        for(int d=epilogue;d>=1;d--){
            int ph=((baseline-d)%8+8)%8;
            int reg=d<=boundary_width?8+boundary_width+d-1:ph;
            vector<State> next;
            for(State x:front){auto ys=step(x,ph,reg,d);next.insert(next.end(),ys.begin(),ys.end());}
            front=unique_states(next);
        }
        for(State x:front){auto it=boundary_id.find({x.h,x.f});if(it!=boundary_id.end())accepting[id].push_back(it->second);}
    }
}

vector<State> run_prologue(int b){
    auto [h,f]=boundaries[b];vector<State> front={{add_lap(h),f}};
    for(int v=0;v<prologue;v++){
        vector<State> next;int reg=v<boundary_width?8+v:v%8;
        for(State x:front){auto ys=step(x,v%8,reg,-1,v==0);next.insert(next.end(),ys.begin(),ys.end());}
        front=unique_states(next);
    }
    return front;
}

vector<int> initial_frontier(int b){
    vector<int> ids;
    for(State s:run_prologue(b)){int id=state_id(s,prologue%8);if(id>=0)ids.push_back(id);}
    int mandatory=baseline-prologue-epilogue;
    for(int i=0;i<mandatory;i++){
        vector<int> next;for(int id:ids)for(int j:adjacency[id])if(j>=0)next.push_back(j);
        ids=unique_ids(next);
    }
    return ids;
}

// Reconstruct one prologue+mandatory-bulk path ending in goal.
vector<int> reconstruct_prefix(int boundary,int goal){
    using P=pair<u32,int>;
    vector<map<P,P>> prologue_prev(prologue);
    auto [h,f]=boundaries[boundary];vector<State> front={{add_lap(h),f}};
    for(int v=0;v<prologue;v++){
        vector<State> next;int reg=v<boundary_width?8+v:v%8;
        for(State x:front)for(State y:step(x,v%8,reg,-1,v==0)){
            if(prologue_prev[v].emplace(P{y.h,y.f},P{x.h,x.f}).second)next.push_back(y);
        }
        front=next;
    }
    vector<int> ids;for(State s:front){int id=state_id(s,prologue%8);if(id>=0)ids.push_back(id);}
    int mandatory=baseline-prologue-epilogue;
    vector<unordered_map<int,int>> previous(mandatory);
    for(int i=0;i<mandatory;i++){
        vector<int> next;for(int id:ids)for(int j:adjacency[id])if(j>=0&&previous[i].emplace(j,id).second)next.push_back(j);
        ids=next;
    }
    vector<int> suffix;int id=goal;
    for(int i=mandatory-1;i>=0;i--){auto [s,p]=decode_state(id);suffix.push_back((s.h>>20)&31);id=previous[i].at(id);}
    reverse(suffix.begin(),suffix.end());
    State s=decode_state(id).first;vector<int> prefix;
    for(int v=prologue-1;v>=0;v--){prefix.push_back((s.h>>20)&31);auto q=prologue_prev[v].at({s.h,s.f});s={q.first,q.second};}
    reverse(prefix.begin(),prefix.end());prefix.insert(prefix.end(),suffix.begin(),suffix.end());return prefix;
}

vector<int> reconstruct_epilogue(int id,int boundary){
    using P=pair<u32,int>;
    vector<map<P,P>> previous(epilogue);
    vector<State> front={decode_state(id).first};
    for(int i=0;i<epilogue;i++){
        int d=epilogue-i,ph=((baseline-d)%8+8)%8;
        int reg=d<=boundary_width?8+boundary_width+d-1:ph;
        vector<State> next;
        for(State x:front)for(State y:step(x,ph,reg,d))if(previous[i].emplace(P{y.h,y.f},P{x.h,x.f}).second)next.push_back(y);
        front=next;
    }
    auto [h,f]=boundaries[boundary];State s{h,f};vector<int> result;
    for(int i=epilogue-1;i>=0;i--){result.push_back((s.h>>20)&31);auto q=previous[i].at({s.h,s.f});s={q.first,q.second};}
    reverse(result.begin(),result.end());return result;
}

struct Witness{int n;vector<int> moves,clause,labels;};
Witness check_actual_play(vector<int> word){
    int n=word.size(),v=0,total_distance=0,turn=0;
    vector<bool> visited(n,false);visited[0]=true;
    Witness w;w.n=n;w.labels=word;set<int> clause;
    int offsets[6]={-3,-5,1,-1,2,-2};
    for(int count=0;count<=n;count++){
        if(lap(word[v])!=total_distance/n)throw runtime_error("witness lap mismatch");
        vector<int> legal;for(int s:{3,5})if(!visited[(v+s)%n])legal.push_back(s);
        int t=type(word[v]);
        if(t==2){
            if(turn!=1||!legal.empty())throw runtime_error("witness terminal mismatch");
            for(int i=0;i<n;i++)if(visited[i]!=(word[i]!=0))throw runtime_error("witness disconnected labels");
            w.clause.assign(clause.begin(),clause.end());return w;
        }
        if(t!=0&&t!=1)throw runtime_error("witness token on empty vertex");
        int s=t==0?3:5;if(find(legal.begin(),legal.end(),s)==legal.end())throw runtime_error("witness illegal move");
        if(turn){
            int reg=v<boundary_width?8+v:(n-v<=boundary_width?8+boundary_width+n-v-1:v%8);
            int pattern=0;for(int i=0;i<6;i++){int target=(v+offsets[i]+n)%n;if(visited[target])pattern|=1<<i;}
            int index=key(reg,pattern,total_distance/n);
            int prescribed=policy[index]=='1'?5:3;
            if(find(legal.begin(),legal.end(),prescribed)==legal.end())prescribed=legal[0];
            if(s!=prescribed)throw runtime_error("witness policy mismatch");
            if(legal.size()==2)clause.insert(policy[index]=='1'?-(index+1):index+1);
        }
        w.moves.push_back(s);total_distance+=s;v=(v+s)%n;visited[v]=true;turn^=1;
    }
    throw runtime_error("witness did not terminate");
}

optional<Witness> find_bad(long long &visits,int &viable,u64 &digest){
    build_graph();int total=adjacency.size();
    vector<int> seen(total,-1),previous(total,-1);visits=0;viable=0;digest=0;
    for(int b=0;b<(int)boundaries.size();b++){
        vector<int> queue;for(int id:initial_frontier(b))if(seen[id]!=b){seen[id]=b;previous[id]=-1;queue.push_back(id);}
        if(!queue.empty())viable++;
        for(size_t qi=0;qi<queue.size();qi++){
            int id=queue[qi];
            if(find(accepting[id].begin(),accepting[id].end(),b)!=accepting[id].end()){
                vector<int> extra;int start=id;
                while(previous[start]>=0){State s=decode_state(start).first;extra.push_back((s.h>>20)&31);start=previous[start];}
                reverse(extra.begin(),extra.end());vector<int> word=reconstruct_prefix(b,start);
                word.insert(word.end(),extra.begin(),extra.end());auto suffix=reconstruct_epilogue(id,b);
                word.insert(word.end(),suffix.begin(),suffix.end());
                return check_actual_play(word);
            }
            for(int next:adjacency[id])if(next>=0&&seen[next]!=b){seen[next]=b;previous[next]=id;queue.push_back(next);}
        }
        visits+=queue.size();
        for(int id:queue)digest^=(u64(b+1)*1000000007ull+id)*0x9e3779b97f4a7c15ull;
    }
    return {};
}

void json_vector(const vector<int>&v){cout<<'[';for(size_t i=0;i<v.size();i++){if(i)cout<<',';cout<<v[i];}cout<<']';}
template<size_t R> bool verify_family(int first,int boundary,const array<u64,R>& table){
    baseline=first;boundary_width=boundary;
    prologue=epilogue=max(5,boundary_width);policy_laps=lap_feature?5:1;
    end_phase=((baseline-epilogue)%8+8)%8;variable_count=(8+2*boundary_width)*64*policy_laps;
    if(baseline%2==0||baseline<prologue+epilogue||boundary_width<1||R!=size_t(8+2*boundary_width))
        throw runtime_error("invalid family parameters");
    policy.assign(variable_count,'0');
    for(int region=0;region<int(R);region++)for(int pattern=0;pattern<64;pattern++)
        if((table[region]>>pattern)&1)policy[region*64+pattern]='1';
    long long visits;int viable;u64 digest;
    auto result=find_bad(visits,viable,digest);
    if(result){
        cout<<"COUNTEREXAMPLE TO THIS FIXED POLICY: n="<<result->n<<"\nmoves=";
        json_vector(result->moves);cout<<"\n";return false;
    }
    cout<<"VERIFIED: second player wins for every n = "<<baseline<<" + 8k, k >= 0\n";
    cout<<"histories="<<histories.size()<<" boundaries="<<boundaries.size()
        <<" bulk_states="<<adjacency.size()<<" viable_boundaries="<<viable
        <<" reachable_pairs="<<visits<<" digest="<<digest<<"\n";
    return true;
}

// Independent ordinary game recursion, normalized so current vertex is 0.
// Each move marks a new vertex and rotates the occupancy mask. Recursion is
// acyclic because the number of marked vertices strictly increases.
bool small_win(u64 occupied,int n,unordered_map<u64,bool>& memo){
    auto found=memo.find(occupied);if(found!=memo.end())return found->second;
    for(int step:{3,5}){
        int destination=step%n;
        if((occupied>>destination)&1)continue;
        u64 next=occupied|(1ull<<destination);
        if(destination)next=(next>>destination)|((next&((1ull<<destination)-1))<<(n-destination));
        if(!small_win(next,n,memo)){memo[occupied]=true;return true;}
    }
    memo[occupied]=false;return false;
}

bool verify_small(){
    cout<<"Exact outcomes n=1,...,33 (P=second player wins):\n";
    for(int n=1;n<=33;n++){
        unordered_map<u64,bool> memo;
        bool first_wins=small_win(1,n,memo);
        bool expected_first=(n%2==0||n==9||n==11||n==17);
        if(first_wins!=expected_first)throw runtime_error("small-case classification mismatch");
        cout<<n<<':'<<(first_wins?'N':'P')<<(n==33?'\n':' ');
    }
    return true;
}

int main(){
    try{
        initialize();
        if(!verify_family(41,16,PREFER5_1))return 1;
        if(!verify_family(19,2,PREFER5_3))return 1;
        if(!verify_family(13,2,PREFER5_5))return 1;
        if(!verify_family(23,4,PREFER5_7))return 1;
        verify_small();
        cout<<"ALL FOUR INFINITE FAMILIES AND ALL SMALL CASES VERIFIED\n";
    }catch(exception&e){cerr<<"ERROR: "<<e.what()<<"\n";return 3;}
}
