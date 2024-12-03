#include <stdio.h>
#include <string.h>
#include <regex.h>
#include <time.h>


void generate_input(char *buffer, size_t size, int n) {
    for (int i = 0; i < n; ++i) {
        buffer[i] = (i % 2 == 0) ? 'a' : 'b'; 
    }
    buffer[n] = '\0';
}

int main() {
    const char *pattern = "^(a|b)*a(a|b)*$";
    regex_t regex;

    // 正規表現のコンパイル
    if (regcomp(&regex, pattern, REG_EXTENDED) != 0) {
        fprintf(stderr, "Failed to compile regex\n");
        return 1;
    }

   
    int n = 20; 
    char input[1000];
    generate_input(input, sizeof(input) - 1, n);

    printf("Testing input of length %d: %s\n", n, input);

    clock_t start = clock();

    int status = regexec(&regex, input, 0, NULL, 0);

    clock_t end = clock();
    double elapsed = (double)(end - start) / CLOCKS_PER_SEC;

    if (status == 0) {
        printf("Match found\n");
    } else {
        printf("No match\n");
    }

    printf("Execution time: %.6f seconds\n", elapsed);

    regfree(&regex);
    return 0;
}
