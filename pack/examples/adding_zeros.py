S = [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

ind = 0
for i in range(3):
    for j in range(4):
        for k in range(4):
            if S[ind] == 0:
                print("ZERO(x_%d_%d_%d);"%(i,j,k))
            else:
                print("NOT_ZERO(x_%d_%d_%d);"%(i,j,k))
            ind += 1
for i in range(3):
    for j in range(4):
        if S[ind] == 0:
            print("ZERO(k_%d_%d_%d);"%(i,j,k))
        else:
            print("NOT_ZERO(k_%d_%d_%d);"%(i,j,k))
        ind += 1

        
