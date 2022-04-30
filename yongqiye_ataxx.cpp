#include <iostream>
#include <string>
#include <cstdlib>
#include <ctime>
#include <map>
#include <cmath>
#include <algorithm>
#include <sys/timeb.h>
#include "jsoncpp/json.h" 
#include <string>
using namespace std;
typedef unsigned long long BitBoard;
typedef unsigned long long ull;
#define BLUE 'B'
#define RED 'R'
#define BLANK ' '
long long times;
int turnID;
struct timeb begintime, midtime;
bool timeout = false;
ull Out0=560802875597055;
ull Out1;
ull Out2;
ull Out4;
BitBoard ALL49;
int xu=1;
BitBoard board_to_bitboard(int board[][10])
{
    BitBoard bb = 0;
    BitBoard c = 1;
    int k = 0;
    for (int i = 7; i >= 1; i--)
    {
        for (int j = 7; j >= 1; j--)
        {
            if (board[i][j] != BLANK)
            {
                bb += c << k;
            }
            k++;
        }
    }
    return bb;
}
BitBoard AllPieces;
BitBoard mask[49];
BitBoard RED_bb;
BitBoard BLUE_bb;
BitBoard Zhufa[49];
BitBoard AI_bb;
BitBoard PLAYER_bb;
BitBoard Change[49];
BitBoard _Change[49];

bool rota=false;
BitBoard NEXT_AI_bb;
BitBoard NEXT_PLAYER_bb;

int AI_COLOR;
int PLAYER_COLOR;

int maxd;
bool if_initial = false;
int startX, startY, resultX, resultY;

//to complate vector
int num = 0;
//to start search algorithm

int turn;
void initialize_mask(BitBoard *bb)
{
    BitBoard b = 1;
    for (int i = 0; i < 49; i++)
    {
        bb[i] = b << i;
    }
}

void intialize_RED(BitBoard &rbb, int board[][10])
{
    rbb = 0;
    int k = 0;
    ull c = 1;
    for (int i = 7; i >= 1; i--)
    {
        for (int j = 7; j >= 1; j--)
        {
            if (board[i][j] == RED)
            {
                rbb += c << k;
            }
            k++;
        }
    }
}
void intialize_BLUE(BitBoard &bbb, int board[][10])
{
    bbb = 0;
    int k = 0;
    ull c = 1;
    for (int i = 7; i >= 1; i--)
    {
        for (int j = 7; j >= 1; j--)
        {
            if (board[i][j] == BLUE)
            {
                bbb += c << k;
            }
            k++;
        }
    }
}
void initialize(); 
bool distance(ull a, ull b)
{
    int hanga, liea;
    liea = a % 7;
    hanga = a / 7;
    int hangb, lieb;
    lieb = b % 7;
    hangb = b / 7;
    if (abs(hangb - hanga) <= 2 && abs(lieb - liea) <= 2)
        return true;
    else
        return false;
}
void initialize_zhufa(BitBoard *bb)
{
    BitBoard mask[49];
    BitBoard temp;
    initialize_mask(mask);
    int pawn_way[24] = {-16, -15, -14, -13, -12, -9, -8, -7, -6, -5, -2, -1, 1, 2, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16};
    for (ull i = 0; i < 49; i++)
    {
        temp = 0;
        for (int k = 0; k < 24; k++)
        {
            if (i + pawn_way[k] >= 0 && i + pawn_way[k] < 49)
            {
                if (distance(i, i + pawn_way[k]))
                {
                    temp |= mask[i + pawn_way[k]];
                }
            }
        }
        bb[i] = temp;
    }
}

void initialize_Change(BitBoard *bb)
{
    BitBoard mask[49];
    BitBoard temp;
    initialize_mask(mask);
    int pawn_way[8] = {-8, -7, -6, -1, 1, 6, 7, 8};
    BitBoard c = 1;
    for (ull i = 0; i < 49; i++)
    {
        temp = 0;
        for (int k = 0; k < 8; k++)
        {
            if (i + pawn_way[k] >= 0 && i + pawn_way[k] < 49)
            {
                if (distance(i, i + pawn_way[k]))
                {
                    temp |= mask[i + pawn_way[k]];
                }
            }
        }
        bb[i] = temp;
        _Change[i]=~Change[i];
    }
}


int dis(int a, int b)
{
    if(mask[a]&Change[b])
        return 1;
    return 2;
}

void bitboard_to_board(BitBoard *mask, int board[][10], BitBoard abb, BitBoard pbb, int AI_COLOR)
{
    int pcolor;
    if (AI_COLOR == RED)
        pcolor = BLUE;
    else
        pcolor = RED;
    for (int i = 0; i < 49; i++)
    {
        if (mask[i] & abb)
        {
            int row = 7 - i / 7;
            int col = 7 - i % 7;
            board[row][col] = AI_COLOR;
        }
        else if (mask[i] & pbb)
        {
            int row = 7 - i / 7;
            int col = 7 - i % 7;
            board[row][col] = pcolor;
        }
        else
        {
            int row = 7 - i / 7;
            int col = 7 - i % 7;
            board[row][col] = BLANK;
        }
    }
}

int currBotColor;         // 我所执子颜色（1为黑，-1为白，棋盘状态亦同）
int gridInfo[7][7] = {0}; // 先x后y，记录棋盘状态
int blackPieceCount = 2, whitePieceCount = 2;
static int delta[24][2] = {{1, 1}, {0, 1}, {-1, 1}, {-1, 0}, {-1, -1}, {0, -1}, {1, -1}, {1, 0}, {2, 0}, {2, 1}, {2, 2}, {1, 2}, {0, 2}, {-1, 2}, {-2, 2}, {-2, 1}, {-2, 0}, {-2, -1}, {-2, -2}, {-1, -2}, {0, -2}, {1, -2}, {2, -2}, {2, -1}};

// 判断是否在地图内
inline bool inMap(int x, int y)
{
    if (x < 0 || x > 6 || y < 0 || y > 6)
        return false;
    return true;
}

// 向Direction方向改动坐标，并返回是否越界
inline bool MoveStep(int &x, int &y, int Direction)
{
    x = x + delta[Direction][0];
    y = y + delta[Direction][1];
    return inMap(x, y);
}

// 在坐标处落子，检查是否合法或模拟落子
bool ProcStep(int x0, int y0, int x1, int y1, int color)
{
    if (color == 0)
        return false;
    if (x1 == -1) // 无路可走，跳过此回合
        return true;
    if (!inMap(x0, y0) || !inMap(x1, y1)) // 超出边界
        return false;
    if (gridInfo[x0][y0] != color)
        return false;
    int dx, dy, x, y, currCount = 0, dir;
    int effectivePoints[8][2];
    dx = abs((x0 - x1)), dy = abs((y0 - y1));
    if ((dx == 0 && dy == 0) || dx > 2 || dy > 2) // 保证不会移动到原来位置，而且移动始终在5×5区域内
        return false;
    if (gridInfo[x1][y1] != 0) // 保证移动到的位置为空
        return false;
    if (dx == 2 || dy == 2) // 如果走的是5×5的外围，则不是复制粘贴
        gridInfo[x0][y0] = 0;
    else
    {
        if (color == 1)
            blackPieceCount++;
        else
            whitePieceCount++;
    }

    gridInfo[x1][y1] = color;
    for (dir = 0; dir < 8; dir++) // 影响邻近8个位置
    {
        x = x1 + delta[dir][0];
        y = y1 + delta[dir][1];
        if (!inMap(x, y))
            continue;
        if (gridInfo[x][y] == -color)
        {
            effectivePoints[currCount][0] = x;
            effectivePoints[currCount][1] = y;
            currCount++;
            gridInfo[x][y] = color;
        }
    }
    if (currCount != 0)
    {
        if (color == 1)
        {
            blackPieceCount += currCount;
            whitePieceCount -= currCount;
        }
        else
        {
            whitePieceCount += currCount;
            blackPieceCount -= currCount;
        }
    }
    return true;
}

int estimation_FUNC();
int _estimation_FUNC();
int estimation_FUNC_NO_WAY(char p, int depth);
void caculate(int board[][10], int AI_COLOR_, int maxdepth);
bool if_end_ai = false;
int startr = -1, startc = -1, endr = -1, endc = -1;

struct mask_pause
{
    vector<int> pawn_way;
    int xu;
    BitBoard mask;
    int max_num;
    int pawn_way_num[24] = {};
};
mask_pause mask_piece[49];
BitBoard mask_p[49];

bool cmp_mp(mask_pause a, mask_pause b)
{
    if(a.max_num!=b.max_num)
    {
        return a.max_num > b.max_num;
    }
    else return a.xu>b.xu;
}
void set_mask_piece()
{
    if (startc == -1 && endc == -1)
    {
        for (int i = 0; i < 49; i++)
        {
            mask_piece[i].mask = mask[i];
            mask_piece[i].xu = 0;
            int pawn_way[24] = {-16, -15, -14, -13, -12, -9, -8, -7, -6, -5, -2, -1, 1, 2, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16};
            for (int j = 0; j < 24; j++)
            {
                mask_piece[i].pawn_way.push_back(pawn_way[j]);
                mask_piece[i].pawn_way_num[j] = -1000000000;
            }
        }
    }
    else
    {
        for (int i = 0; i < 49; i++)
        {
            for (int j = 22; j >= 0; j--)
            {
                for (int u = 0; u <= j; u++)
                {
                    if (mask_piece[i].pawn_way_num[u] < mask_piece[i].pawn_way_num[u + 1])
                    {
                        int temp = mask_piece[i].pawn_way_num[u];
                        mask_piece[i].pawn_way_num[u] = mask_piece[i].pawn_way_num[u + 1];
                        mask_piece[i].pawn_way_num[u + 1] = temp;
                        temp = mask_piece[i].pawn_way[u];
                        mask_piece[i].pawn_way[u] = mask_piece[i].pawn_way[u + 1];
                        mask_piece[i].pawn_way[u + 1] = temp;
                    }
                }
            }
            mask_piece[i].max_num = mask_piece[i].pawn_way_num[0];
            for (int j = 0; j < 24; j++)
            {
                mask_piece[i].pawn_way_num[j] = -1000000000;
            }
        }
        sort(mask_piece, mask_piece + 49, cmp_mp);
        for(int i=0;i<49;i++)mask_piece[i].xu=0;
        xu=1;
    }
}
void set_mask_p()
{
    for (int i = 0; i < 49; i++)
    {
        mask_p[i] = mask_piece[i].mask;
    }
}
void write()
{
    Json::Value ret;
    ret["response"]["x0"] = startX;
    ret["response"]["y0"] = startY;
    ret["response"]["x1"] = resultX;
    ret["response"]["y1"] = resultY;
    Json::FastWriter writer;
    cout << writer.write(ret) << endl;
}
inline int AlphaBeta(int depth, int alpha, int beta, char p) //p=a for ai, p=p for player
{
    times++;

    if((times%40000)==0)
    {
        ftime(&midtime);
        if ((midtime.time - begintime.time) * 1000 + midtime.millitm - begintime.millitm >= 995)
        {
            if(rota)
            {
                startX=(8-startr)-1;
                startY=(startc)-1;
                resultX=(8-endr)-1;
                resultY=endc-1;
            }
            else startX = startc - 1, startY = startr - 1, resultX = endc - 1, resultY = endr - 1;
            write();
            system("pause");
            exit(0);
        }
    }
    if (depth == 0)
    {
        if (maxd % 2 )
            return _estimation_FUNC();
        else
            return estimation_FUNC();
    }
    bool fFoundPv=false;
    ull blank=ALL49^AllPieces;
    if (p == 'a')
    {

        if (depth == maxd)
        {
            bool if_no_way = true;
            BitBoard record=0;
            for (int k = 0; k < 24; k++)
            {
                for (int i = 0; i < 49; i++)
                {
                    BitBoard so;
                    so = mask_p[i] & AI_bb;
                    if (so == 0)
                        continue;
                    int pi = __builtin_ctzll(mask_p[i]);
                    BitBoard Zhu = Zhufa[pi] & (blank);
                    Zhu-=(Change[pi]&record);
                    int pak=mask_piece[i].pawn_way[k];
                    if (pi + pak >= 0 && pi + pak < 49)
                    {
                        BitBoard zou = mask[pi + pak] & Zhu;
                        if (zou == 0)
                        {      
                            continue;
                        }
                        int ios = __builtin_ctzll(zou);
                        int dist = dis(ios, pi);
                        BitBoard AI_bb_temp = AI_bb;
                        BitBoard PLAYER_bb_temp = PLAYER_bb;
                        if (dist == 1)
                        {
                            PLAYER_bb = ((_Change[ios]) & PLAYER_bb);
                            AI_bb = AllPieces-PLAYER_bb;
                            AI_bb += mask[ios];
                            record|=mask[ios];
                        }
                        //make next move
                        else if (dist == 2)
                        {
                            PLAYER_bb = (_Change[ios]) & PLAYER_bb;
                            AI_bb = AllPieces-PLAYER_bb;
                            AI_bb = AI_bb - mask[pi] + mask[ios];
                        }
                        if_no_way = false;
                        BitBoard AllPieces_temp = AllPieces;
                        AllPieces = AI_bb + PLAYER_bb;
                        BitBoard NEXT_AI_bb_temp = AI_bb;
                        BitBoard NEXT_PLAYER_bb_temp = PLAYER_bb;
                        int value;
                        if (fFoundPv)
                        {
                            value = -AlphaBeta(depth - 1, -alpha - 1, -alpha, 'p');
                            if ((value > alpha) && (value < beta))
                            {
                                value = -AlphaBeta(depth - 1, -beta, -alpha, 'p');
                            }
                        }
                        else
                            value = -AlphaBeta(depth - 1, -beta, -alpha, 'p');
                        AllPieces = AllPieces_temp;
                        AI_bb = AI_bb_temp;
                        PLAYER_bb = PLAYER_bb_temp;
                        //unmake last move

                        if (depth == maxd)
                        {
                            mask_piece[i].pawn_way_num[k] = value;
                        }
                        if (value >= beta)
                        {
                            return beta;
                        }
                        if (value > alpha)
                        {
                            alpha = value;
                            fFoundPv=true;
                            NEXT_AI_bb = NEXT_AI_bb_temp;
                            NEXT_PLAYER_bb = NEXT_PLAYER_bb_temp;
                            startr = 7 - pi / 7;
                            startc = 7 - pi % 7;
                            endr = 7 - ios / 7;
                            endc = 7 - ios % 7;
                            mask_piece[i].xu=xu++;
                        }
                    }
                }
            }
            if (if_no_way)
            {
                return estimation_FUNC_NO_WAY('a', depth);
            }
            return alpha;
        }
        else
        {
            bool if_no_way = true;
            BitBoard ai_temp = AI_bb;
            BitBoard record=0;
            while (ai_temp)
            {
                int pi = __builtin_ctzll(ai_temp);
                ai_temp -= mask[pi];
                BitBoard Zhu = Zhufa[pi] & (blank);
                Zhu-=(Change[pi]&record);
                while (Zhu)
                {
                    int ios = __builtin_ctzll(Zhu);
                    Zhu = Zhu - mask[ios];
                    int dist = dis(ios, pi);
                    BitBoard AI_bb_temp = AI_bb;
                    BitBoard PLAYER_bb_temp = PLAYER_bb;
                    if (dist == 1)
                    {
                        PLAYER_bb = ((_Change[ios]) & PLAYER_bb);
                        AI_bb = AllPieces-PLAYER_bb;
                        AI_bb += mask[ios];
                        record|=mask[ios];
                    }
                    //make next move
                    else if (dist == 2)
                    {
                        PLAYER_bb = (_Change[ios]) & PLAYER_bb;
                        AI_bb = AllPieces-PLAYER_bb;
                        AI_bb = AI_bb - mask[pi] + mask[ios];
                    }

                    if_no_way = false;
                    BitBoard AllPieces_temp = AllPieces;
                    AllPieces = AI_bb + PLAYER_bb;
                    BitBoard NEXT_AI_bb_temp = AI_bb;
                    BitBoard NEXT_PLAYER_bb_temp = PLAYER_bb;
                    int value;
                    if (fFoundPv)
                    {
                        value = -AlphaBeta(depth - 1, -alpha - 1, -alpha, 'p');
                        if ((value > alpha) && (value < beta))
                        {
                            value = -AlphaBeta(depth - 1, -beta, -alpha, 'p');
                        }
                    }
                    else
                        value = -AlphaBeta(depth - 1, -beta, -alpha, 'p');
                    AllPieces = AllPieces_temp;
                    AI_bb = AI_bb_temp;
                    PLAYER_bb = PLAYER_bb_temp;
                    //unmake last move
                    if (value >= beta)
                    {
                        return beta;
                    }
                    if (value > alpha)
                    {
                        alpha = value;
                        fFoundPv = true;
                    }
                }
            }
            if (if_no_way)
            {
                return estimation_FUNC_NO_WAY('a', depth);
            }
            return alpha;
        }
    }
    else if (p == 'p')
    {
        bool if_no_way = true;
        BitBoard pl_temp = PLAYER_bb;
        BitBoard record=0;//have placed
        while (pl_temp != 0)
        {
            int i = __builtin_ctzll(pl_temp);
            pl_temp -= mask[i];
            BitBoard Zhu = Zhufa[i] & (blank);
            Zhu-=(Change[i]&record);
            while (Zhu != 0)
            {
                if_no_way = false;
                int ios = __builtin_ctzll(Zhu);
                Zhu -= mask[ios];
                int dist = dis(ios, i);
                BitBoard AI_bb_temp = AI_bb;
                BitBoard PLAYER_bb_temp = PLAYER_bb;
                if (dist == 1)
                    {
                        AI_bb = ((_Change[ios]) & AI_bb);
                        PLAYER_bb = AllPieces-AI_bb;
                        PLAYER_bb += mask[ios];
                        record|=mask[ios];
                    }
                    //make next move
                else if (dist == 2)
                    {
                        AI_bb = (_Change[ios]) & AI_bb;
                        PLAYER_bb = AllPieces-AI_bb;
                        PLAYER_bb = PLAYER_bb - mask[i] + mask[ios];
                    }
                BitBoard AllPieces_temp = AllPieces;
                AllPieces = AI_bb + PLAYER_bb;
                int value;
                if (fFoundPv)
                {
                     value = -AlphaBeta(depth - 1, -alpha - 1, -alpha, 'a');
                    if ((value > alpha) && (value < beta))
                    { // 检查失败
                        value = -AlphaBeta(depth - 1, -beta, -alpha, 'a');
                    }
                }
                else
                    value = -AlphaBeta(depth - 1, -beta, -alpha, 'a');
                
                AllPieces = AllPieces_temp;
                AI_bb = AI_bb_temp;
                PLAYER_bb = PLAYER_bb_temp;
                //unmake last move

                if (value >= beta)
                {
                    return beta;
                }
                if (value > alpha)
                {
                    alpha = value;
                    fFoundPv=true;
                }
            }
        }
        if (if_no_way)
        {
            return estimation_FUNC_NO_WAY('p', depth);
        }
        return alpha;
    }
}
ull right76=279258638311359;
ull left76=558517276622718;
ull right75=137412980756383;
ull left75=549651923025532;
ull blank;
inline int stablea()
{
        blank=ALL49^(AllPieces);
        ull PL_move=PLAYER_bb;
        PL_move|=(PL_move>>1)&right76;
        PL_move|=(PL_move>>1)&right76;
        PL_move|=(PL_move*2)&left76;
        PL_move|=(PL_move*2)&left76;
        PL_move|=PL_move<<7;
        PL_move|=PL_move<<7;
        PL_move|=PL_move>>14;
        PL_move&=blank;
        PL_move|=(PL_move>>1)&right76;
        PL_move|=(PL_move*2)&left76;
        PL_move|=PL_move<<7;
        PL_move|=PL_move>>7;
        return __builtin_popcountll(AI_bb&(ALL49^PL_move));
}
inline int stablep()
{
        ull AI_move=AI_bb;
        AI_move|=(AI_move>>1)&right76;
        AI_move|=(AI_move>>1)&right76;
        AI_move|=(AI_move*2)&left76;
        AI_move|=(AI_move*2)&left76;
        AI_move|=AI_move<<7;
        AI_move|=AI_move<<7;
        AI_move|=AI_move>>14;
        AI_move&=blank;
        AI_move|=(AI_move>>1)&right76;
        AI_move|=(AI_move*2)&left76;
        AI_move|=AI_move<<7;
        AI_move|=AI_move>>7;
        return __builtin_popcountll(PLAYER_bb&(ALL49^AI_move));
}


inline int estimation_FUNC()
{
        return (__builtin_popcountll(AI_bb)*2+__builtin_popcountll(AI_bb&Out1)+__builtin_popcountll(AI_bb&Out0)*2-(__builtin_popcountll(PLAYER_bb&Out0)*2+__builtin_popcountll(PLAYER_bb)*2+__builtin_popcountll(PLAYER_bb&Out1)))*4+(stablea()-stablep())*6;
}
inline int _estimation_FUNC()
{
        return (-(__builtin_popcountll(AI_bb)*2+__builtin_popcountll(AI_bb&Out1)+__builtin_popcountll(AI_bb&Out0)*2)+__builtin_popcountll(PLAYER_bb)*2+__builtin_popcountll(PLAYER_bb&Out1)+__builtin_popcountll(PLAYER_bb&Out0)*2)*4+(stablep()-stablea())*6;
}
inline int sign(int a)
{
    if(a>0)return 1;
    return -1;
}
inline int estimation_FUNC_NO_WAY(char p, int depth)
{
	if (p == 'p')
        return (-__builtin_popcountll(AI_bb)+__builtin_popcountll(PLAYER_bb)+__builtin_popcountll(AllPieces)-49)*(depth*depth)*5000;
	else
        return (__builtin_popcountll(AI_bb)-__builtin_popcountll(PLAYER_bb)+__builtin_popcountll(AllPieces)-49)*(depth*depth)*5000;
}
void caculate(int board[][10], int AI_COLOR_, int maxdepth)
{
    int alpha = -2000000000;
    int beta = 2000000000;
    maxd = maxdepth;
    set_mask_piece();
    set_mask_p();
    int a = AlphaBeta(maxd, alpha, beta, 'a');
}

int main()
{
    Out1=2139502452480;
    Out2=7558594560+16777216;
    ALL49=562949953421311;
    int x0, y0, x1, y1;
    int board[10][10];
    // 初始化棋盘
    gridInfo[0][0] = gridInfo[6][6] = 1;  //|黑|白|
    gridInfo[6][0] = gridInfo[0][6] = -1; //|白|黑|
    initialize();
    // 读入JSON
    string str;
    getline(cin, str);
    Json::Reader reader;
    Json::Value input;
    reader.parse(str, input);

    // 分析自己收到的输入和自己过往的输出，并恢复状态
    turnID = input["responses"].size();
    currBotColor = input["requests"][(Json::Value::UInt)0]["x0"].asInt() < 0 ? 1 : -1; // 第一回合收到坐标是-1, -1，说明我是黑方
    if (currBotColor == 1)
    {
        AI_COLOR = RED;
        PLAYER_COLOR = BLUE;
    }
    else
    {
        AI_COLOR = BLUE;
        PLAYER_COLOR = RED;
    }
    int t = 0;
    for (int i = 0; i < turnID; i++)
    {
        // 根据这些输入输出逐渐恢复状态到当前回合
        x0 = input["requests"][i]["x0"].asInt();
        y0 = input["requests"][i]["y0"].asInt();
        x1 = input["requests"][i]["x1"].asInt();
        y1 = input["requests"][i]["y1"].asInt();
        if (x1 >= 0)
        {
            ProcStep(x0, y0, x1, y1, -currBotColor); // 模拟对方落子
        }
        x0 = input["responses"][i]["x0"].asInt();
        y0 = input["responses"][i]["y0"].asInt();
        x1 = input["responses"][i]["x1"].asInt();
        y1 = input["responses"][i]["y1"].asInt();
        if (x1 >= 0)
        {
            ProcStep(x0, y0, x1, y1, currBotColor); // 模拟己方落子
        }
    }

    // 看看自己本回合输入
    x0 = input["requests"][turnID]["x0"].asInt();
    y0 = input["requests"][turnID]["y0"].asInt();
    x1 = input["requests"][turnID]["x1"].asInt();
    y1 = input["requests"][turnID]["y1"].asInt();
    if (x1 >= 0)
    {
        ProcStep(x0, y0, x1, y1, -currBotColor); // 模拟对方落子
    }

    ftime(&begintime);
    //if(AI_COLOR==BLUE)rota=true;
    // 做出决策（你只需修改以下部分）
    board[10][10] = {};
    int numred = 0, numblue = 0;
    for (int r = 1; r <= 7; r++)
    {
        for (int c = 1; c <= 7; c++)
        {
            if (gridInfo[c - 1][r - 1] == 1)
            {
                if(rota)
                {
                    board[8-c][r]=RED;
                }
                else board[r][c] = RED;
                numred++;
            }
            else if (gridInfo[c - 1][r - 1] == -1)
            {
                if(rota)
                {
                    board[8-c][r]=BLUE;
                }
                else board[r][c] = BLUE;
                numblue++;
            }
            else
            {
                if(rota)
                {
                    board[8-c][r]=BLANK;
                }
                else board[r][c] = BLANK;
            }
        }
    }
    intialize_RED(RED_bb, board);
    intialize_BLUE(BLUE_bb, board);
    AllPieces=RED_bb|BLUE_bb;
        if (AI_COLOR == RED)
    {
        AI_bb = RED_bb;
        PLAYER_bb = BLUE_bb;
        PLAYER_COLOR = BLUE;
    }
    else
    {
        AI_bb = BLUE_bb;
        PLAYER_bb = RED_bb;
        PLAYER_COLOR = RED;
    }

    for(int i=4;i<=20;i++)
    {
       caculate(board, AI_COLOR, i);
        if(rota)
        {
            startX=(8-startr)-1;
            startY=(startc)-1;
            resultX=(8-endr)-1;
            resultY=endc-1;
        }
        else startX = startc - 1, startY = startr - 1, resultX = endc - 1, resultY = endr - 1;
    }    
    write();
    system("pause");
}
void initialize()
{
    initialize_mask(mask);
    initialize_zhufa(Zhufa);
    initialize_Change(Change);
}