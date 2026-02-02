/* BBS Door */
#include <stdio.h>
int is_bdi(int n) { return (n % 10) == 3; }
int main() {
    printf("╔══════════════════════════╗\n");
    printf("║ MONSTER CATEGORY THEORY ║\n");
    printf("╚══════════════════════════╝\n");
    int n; scanf("%d", &n);
    if (is_bdi(n)) printf("🌳 I ARE LIFE!\n");
    return 0;
}
