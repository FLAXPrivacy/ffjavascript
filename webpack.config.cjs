const path = require("path");
const webpack = require("webpack");

module.exports = {
  entry: "./main.js",
  output: {
    filename: "main.cjs",
    path: path.resolve(__dirname, "build"),
    library: "ffjavascript",
    libraryTarget: "var",
  },
  resolve: {
    fallback: {
      buffer: require.resolve("buffer/"),
      crypto: require.resolve("crypto-browserify"),
      stream: require.resolve("stream-browserify"),
      os: require.resolve("os-browserify"),
    },
  },
  plugins: [
    new webpack.ProvidePlugin({
      Buffer: ["buffer", "Buffer"],
    }),
    new webpack.ProvidePlugin({
      crypto: "crypto-browserify",
    }),
  ],
};
