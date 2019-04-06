import React, { Component, createContext } from "react";

export const SettingsContext = createContext();

const toggle = (dis, key) => value => {
  dis.setState(state => ({ [key]: value || !state[key] }));
};

class SettingsProvider extends Component {
  state = {
    scale: 1,
    crt: false,
    fullScreen: false,
    isMobile: false
  };

  toggleCrt = toggle(this, "crt");
  toggleFullScreen = toggle(this, "fullScreen");
  toggleMobile = toggle(this, "isMobile");
  changeScale = toggle(this, "scale");

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
