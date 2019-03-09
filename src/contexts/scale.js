import React, { Component, createContext } from "react";

export const ScaleContext = createContext();

class ScaleProvider extends Component {
  state = {
    scale: 2,
    // changeScale: val =>
    //   typeof val === "number" ? this.setState(() => ({ scale: val })) : null
    changeScale: () => {
      this.setState(() => ({ scale: this.state.scale === 1 ? 2 : 1 }));
    }
  };
  render() {
    return (
      <ScaleContext.Provider value={this.state}>
        {this.props.children}
      </ScaleContext.Provider>
    );
  }
}

export default ScaleProvider;
