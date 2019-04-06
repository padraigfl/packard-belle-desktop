import React, { Component, createContext } from "react";

export const SettingsContext = createContext();

const toggle = (dis, val) => () => dis.setState(state => !dis[val]);

class SettingsProvider extends Component {
  state = {
    scale: 1,
    crt: false,
    fullScreen: false,
    isMobile: false
  };

  changeScale = () => {
    this.setState(() => ({ scale: this.state.scale === 1 ? 2 : 1 }));
  };

  toggleCrt = toggle(this, "crt");
  toggleFullScreen = toggle(this, "fullScreen");
  toggleMobile = toggle(this, "isMobile");

  render() {
    const { changeScale, toggleCrt, toggleFullScreen, toggleMobile } = this;
    const context = {
      ...this.state,
      changeScale,
      toggleCrt,
      toggleFullScreen,
      toggleMobile
    };
    return (
      <SettingsContext.Provider value={context}>
        {this.props.children}
      </SettingsContext.Provider>
    );
  }
}

export default SettingsProvider;
