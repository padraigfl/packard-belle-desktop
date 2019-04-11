import React, { Component, createContext } from "react";

export const SettingsContext = createContext();

const toggle = (dis, key) => () => {
  dis.setState(state => ({ [key]: !state[key] }));
};

const setKeyValue = (dis, key) => val => {
  dis.setState(state => ({ [key]: val }));
};

class SettingsProvider extends Component {
  state = {
    scale: 1,
    crt: true,
    fullScreen: false,
    isMobile: false,
    bgImg: window && window.localStorage.getItem("bgImg"),
    bgStyle: window && window.localStorage.getItem("bgStyle")
  };

  toggleCrt = toggle(this, "crt");
  toggleFullScreen = toggle(this, "fullScreen");
  toggleMobile = toggle(this, "isMobile");
  changeScale = setKeyValue(this, "scale");

  updateBackgroundImage = () => {
    if (window && window.localStorage) {
      const bgImg = window.localStorage.getItem("bgImg");
      const bgStyle = window.localStorage.getItem("bgStyle");
      if (bgImg) {
        this.setState({ bgImg, bgStyle });
      }
    }
  };

  render() {
    const {
      changeScale,
      toggleCrt,
      toggleFullScreen,
      toggleMobile,
      updateBackgroundImage
    } = this;
    const context = {
      ...this.state,
      changeScale,
      toggleCrt,
      toggleFullScreen,
      toggleMobile,
      updateBackgroundImage
    };
    return (
      <SettingsContext.Provider value={context}>
        {this.props.children}
      </SettingsContext.Provider>
    );
  }
}

export default SettingsProvider;
