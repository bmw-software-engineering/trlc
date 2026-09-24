export default {
    plugins: ["./src/index.js"],
    overrides: [
        {
            files: ["*.trlc", "*.rsl"],
            options: {
                parser: "trlc",
                tabWidth: 4,
            },
        },
    ],
};
